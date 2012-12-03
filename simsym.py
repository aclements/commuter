"""Simple symbolic execution engine for Python."""

import sys
import os
import z3
import types

# This maintains a type hierarchy that parallels Z3's symbolic type
# hierarchy.  Each type wraps the equivalent Z3 type and defers to the
# Z3 methods for all symbolic operations (wrapping the results in the
# appropriate wrapper type).  However, these types add methods
# specific to symbolic execution; most notably __nonzero__.

# Monkey-patch __nonzero__ on Z3 types to make sure we don't
# accidentally call it instead of our wrappers.
def z3_nonzero(self):
    raise RuntimeError("Cannot __nonzero__ a %s" % self.__class__)
z3.ExprRef.__nonzero__ = z3_nonzero
del z3_nonzero

class Symbolic(object):
    """Root of the symbolic type wrapper hierarchy."""
    pass

class SymbolicVal(object):
    """A symbolic value with a specific type (or "sort" in z3
    terminology).  A subclass of SymbolicVal must have a _z3_sort
    class field giving the z3.SortRef for the value's type."""

    @classmethod
    def any(cls, name):
        """Return a symbolic constant of unknown value."""
        # Const returns the most specific z3.*Ref type it can based on
        # the sort.
        return cls(z3.Const(name, cls._z3_sort))

class MetaZ3Wrapper(type):
    """Metaclass to generate wrappers for Z3 ref methods.  The class
    should have a __wrap__ dictionary mapping from (wrapper class
    name, argument count) pairs to a list of method names to wrap.
    This will generate all of the named methods, calling the
    corresponding method on self._v, and wrapping the result using the
    named wrapper class."""

    def __new__(cls, classname, bases, classdict):
        if "__wrap__" in classdict:
            for (wrapper, nargs), methods in classdict.pop("__wrap__").items():
                for method in methods:
                    args = ["o%d" % i for i in range(nargs - 1)]
                    code = "def %s(%s):\n" % (method, ",".join(["self"] + args))
                    for o in args:
                        code += " if isinstance(%s, Symbolic): %s=%s._v\n" % \
                            (o, o, o)
                    code += " return %s(self._v.%s(%s))" % \
                        (wrapper or "", method, ",".join(args))
                    locals_dict = {}
                    exec code in globals(), locals_dict
                    classdict[method] = locals_dict[method]

        return type.__new__(cls, classname, bases, classdict)

class SExpr(Symbolic):
    __metaclass__ = MetaZ3Wrapper

    def __init__(self, ref):
        if not isinstance(ref, z3.ExprRef):
            raise TypeError("SExpr expected ExprRef, got %s" % strtype(ref))
        self._v = ref

    __wrap__ = {("wrap", 2): ["__eq__", "__ne__"],
                (None, 1): ["__str__", "__repr__"]}

class SArith(SExpr):
    def __init__(self, ref):
        if not isinstance(ref, z3.ArithRef):
            raise TypeError("SArith expected ArithRef, got %s" % strtype(ref))
        super(SArith, self).__init__(ref)

    __wrap__ = {("wrap", 2):
                    ["__add__", "__div__", "__mod__", "__mul__", "__pow__",
                     "__sub__", "__truediv__",
                     "__radd__", "__rdiv__", "__rmod__", "__rmul__", "__rpow__",
                     "__rsub__", "__rtruediv__",
                     "__ge__", "__gt__", "__le__", "__lt__"],
                ("wrap", 1):
                    ["__neg__", "__pos__"]}

class SInt(SArith, SymbolicVal):
    _z3_sort = z3.IntSort()

class SBool(SExpr, SymbolicVal):
    _z3_sort = z3.BoolSort()

    def __init__(self, ref):
        if not isinstance(ref, z3.BoolRef):
            raise TypeError("SBool expected BoolRef, got %s" % strtype(ref))
        super(SBool, self).__init__(ref)

    def __nonzero__(self):
        solver = get_solver()
        solver.push()
        solver.add(self._v)
        c = solver.check()
        if c == z3.unknown:
            raise RuntimeError('Undecidable constraints')
        canTrue = (c == z3.sat)
        solver.pop()

        solver.push()
        solver.add(z3.Not(self._v))
        c = solver.check()
        if c == z3.unknown:
            raise RuntimeError('Undecidable constraints')
        canFalse = (c == z3.sat)
        solver.pop()

        if canTrue and not canFalse:
            return True
        if canFalse and not canTrue:
            return False
        if not canTrue and not canFalse:
            raise RuntimeError("Branch contradiction")

        # Both are possible; take both paths
        global cursched
        global curschedidx
        if len(cursched) == curschedidx:
            newsched = list(cursched)
            cursched.append(True)
            newsched.append(False)
            queue_schedule(newsched)

        rv = cursched[curschedidx]
        if rv == True:
            solver.add(self._v)
        else:
            solver.add(z3.Not(self._v))
        curschedidx = curschedidx + 1
        return rv

#
# Constructors
#

def symand(exprlist):
    if any([isinstance(x, Symbolic) for x in exprlist]):
        return wrap(z3.And(*[unwrap(x) for x in exprlist]))
    else:
        return all(exprlist)

def symor(exprlist):
    if any([isinstance(x, Symbolic) for x in exprlist]):
        return wrap(z3.Or(*[unwrap(x) for x in exprlist]))
    else:
        return any(exprlist)

def symnot(e):
    if isinstance(e, Symbolic):
        return wrap(z3.Not(unwrap(e)))
    else:
        return not e

def symeq(a, b):
    if isinstance(a, tuple) and isinstance(b, tuple):
        if len(a) != len(b):
            return False
        return symand([symeq(aa, bb) for (aa, bb) in zip(a, b)])
    return a == b

#
# Conversions to Z3 types and wrapper types
#

def unwrap(val):
    """Convert a value to a Z3 value.

    If val is a simsym.Symbolic, returns the wrapped Z3 value.
    Otherwise, simply returns val."""

    if isinstance(val, Symbolic):
        return val._v
    return val

def wrap(ref):
    """Convert a value to a simsym.Symbolic.

    If ref is a Z3 symbolic value, wraps it in a simsym.Symbolic.
    Otherwise, if ref is a concrete type supported by the symbolic
    engine, returns value.  Otherwise, raises TypeError."""

    if isinstance(ref, (bool, int, long, float)):
        # Concrete type supported by Z3
        return ref

    if not isinstance(ref, z3.ExprRef):
        raise TypeError("Not a bool, int, long, float, or z3.ExprRef")

    if isinstance(ref, z3.ArithRef):
        return SArith(ref)
    if isinstance(ref, z3.BoolRef):
        return SBool(ref)
    return SExpr(ref)

#
# AST matching code.  Unused because the simplifier aggressively
# rewrites things back to its own preferred representation, and
# it is difficult to rewrite just one child in an AST (no generic
# AST node constructors).
#

def matchvar(n):
    return z3.Int('@match:%s' % n)

def ast_match2(a, pat, matchvars):
    if pat.decl().name().startswith('@match:'):
        varname = pat.decl().name()[7:]
        cur = matchvars.get(varname, None)
        if cur is None:
            matchvars[varname] = a
            return True
        return cur.eq(a)

    if a.__class__ != pat.__class__: return False
    if not a.decl().eq(pat.decl()): return False
    if a.num_args() != pat.num_args(): return False
    for (aa, pa) in zip(a.children(), pat.children()):
        if not ast_match2(aa, pa, matchvars): return False
    return True

def ast_match(a, pat, matchvars):
    matchvars.clear()
    return ast_match2(a, pat, matchvars)

def ast_cleanup(a):
    matchvars = {}
    if ast_match(a, z3.Not(matchvar('a') == matchvar('b')), matchvars):
        return matchvars['a'] != matchvars['b']
    return a

#
# Symbolic executor
#

solver = None
assumptions = None
schedq = []
cursched = None
curschedidx = None

def get_solver():
    """Return the current z3.Solver(), or raise RuntimeError if no
    solver is active."""
    if solver is None:
        raise RuntimeError("Symbolic execution attempted outside symbolic_apply")
    return solver

def queue_schedule(s):
    # print "currently in schedule", cursched
    # print "queueing schedule", s
    schedq.append(s)

def str_state():
    """Return the current path constraint as a string, or None if the
    path is unconstrained."""

    asserts = get_solver().assertions()
    if len(asserts) == 0:
        return None
    return str(z3.simplify(z3.And(*asserts),
                           expand_select_store=True))

def simplify(expr):
    t = z3.Repeat(z3.Then('propagate-values',
                          'ctx-solver-simplify',
                          z3.With('simplify', expand_select_store=True)))
    subgoals = t(unwrap(expr))
    if len(subgoals[0]) == 0:
        s = wrap(z3.BoolVal(True))
    else:
        s = wrap(z3.simplify(z3.And(*[z3.And(*g) for g in subgoals])))
    return s

def require(e):
    """Declare symbolic expression e to be True."""

    if e is True:
        return
    if any(unwrap(e).eq(a) for a in assumptions):
        return

    solver = get_solver()
    solver.add(unwrap(e))
    sat = solver.check()
    if sat == z3.unsat:
        raise RuntimeError("Unsatisfiable assumption %s" % e)
    elif sat != z3.sat:
        raise RuntimeError("Uncheckable assumption %s" % e)

def assume(e):
    require(e)
    assumptions.append(unwrap(e))

def symbolic_apply(fn, *args):
    """Evaluate fn(*args) under symbolic execution.  The return value
    of fn is ignored because it may have many return values."""

    rvs = []
    queue_schedule([])

    global schedq
    while len(schedq) > 0:
        global cursched
        cursched = schedq.pop()

        global curschedidx
        curschedidx = 0

        global solver
        global assumptions
        solver = z3.Solver()
        assumptions = []
        try:
            rv = fn(*args)
            condlist = [a for a in solver.assertions()
                        if not any(a.eq(u) for u in assumptions)]
            cond = wrap(z3.And(*([z3.BoolVal(True)] + condlist)))
            rvs.append((cond, rv))
        except Exception as e:
            if len(e.args) == 1:
                e.args = ('%s in symbolic state:\n%s' % (e.args[0], str_state()),)
            else:
                e.args = e.args + (str_state(),)
            raise
        finally:
            solver = None
            assumptions = None
    return rvs

def combine(rvs):
    """Given a set of return values from symbolic_apply, combine
    the conditions for identical return values."""

    combined = []
    used = [False] * len(rvs)
    for idx, (cond, rv) in enumerate(rvs):
        if used[idx]:
            continue
        used[idx] = True
        for idx2, (cond2, rv2) in enumerate(rvs):
            if used[idx2]:
                continue
            solver = z3.Solver()
            e = symnot(symeq(rv, rv2))
            solver.add(unwrap(e))
            c = solver.check()
            if c == z3.unsat:
                used[idx2] = True
                cond = wrap(z3.Or(unwrap(cond), unwrap(cond2)))
        combined.append((cond, rv))
    return combined

#
# Utilities
#

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__
