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

    __wrap__ = {("make_sexpr", 2): ["__eq__", "__ne__"],
                (None, 1): ["__str__", "__repr__"]}

class SArith(SExpr):
    def __init__(self, ref):
        if not isinstance(ref, z3.ArithRef):
            raise TypeError("SArith expected ArithRef, got %s" % strtype(ref))
        super(SArith, self).__init__(ref)

    __wrap__ = {("make_sexpr", 2):
                    ["__add__", "__div__", "__mod__", "__mul__", "__pow__",
                     "__sub__", "__truediv__",
                     "__radd__", "__rdiv__", "__rmod__", "__rmul__", "__rpow__",
                     "__rsub__", "__rtruediv__",
                     "__ge__", "__gt__", "__le__", "__lt__"],
                ("make_sexpr", 1):
                    ["__neg__", "__pos__"]}

class SBool(SExpr):
    def __init__(self, ref):
        if not isinstance(ref, z3.BoolRef):
            raise TypeError("SBool expected BoolRef, got %s" % strtype(ref))
        super(SBool, self).__init__(ref)

    def __nonzero__(self):
        solver.push()
        solver.add(self._v)
        # XXX What about z3.unknown?
        canTrue = (solver.check() == z3.sat)
        solver.pop()

        solver.push()
        solver.add(z3.Not(self._v))
        canFalse = (solver.check() == z3.sat)
        solver.pop()

        if canTrue and not canFalse:
            return True
        if canFalse and not canTrue:
            return False
        if not canTrue and not canFalse:
            raise RuntimeError("Branch contradiction")

        # Both are possible; take both paths
        # XXX os.fork might prove too expensive.  Alternatively, we
        # could replay our path from the beginning, which would also
        # let us return symbolic and non-picklable values to concrete
        # space and implement a counter-example cache.
        child = os.fork()
        if child == 0:
            # True path
            solver.add(self._v)
            return True
        # False path
        os.waitpid(child, 0)
        solver.add(z3.Not(self._v))
        return False

#
# Constructors
#

def anyInt(name):
    """Return a symbolic value that can be any integer."""
    return make_sexpr(z3.Int(name))

#
# Conversions to Z3 types and wrapper types
#

def toz3(val):
    if isinstance(val, Symbolic):
        return val._v
    return val

def make_sexpr(ref):
    ## handle concrete types
    if isinstance(ref, bool):
        return ref

    if isinstance(ref, z3.ArithRef):
        return SArith(ref)
    if isinstance(ref, z3.BoolRef):
        return SBool(ref)
    return SExpr(ref)

#
# Symbolic executor
#

solver = z3.Solver()

def str_state():
    """Return the current path constraint as a string, or None if the
    path is unconstrained."""

    asserts = solver.assertions()
    if len(asserts) == 0:
        return None
    return str(z3.simplify(z3.And(*asserts)))

def assume(e):
    """Declare symbolic expression e to be True."""

    solver.add(toz3(e))
    sat = solver.check()
    if sat == z3.unsat:
        raise RuntimeError("Unsatisfiable assumption")
    elif sat != z3.sat:
        raise RuntimeError("Uncheckable assumption")

def symbolic_apply(fn, *args):
    """Evaluate fn(*args) under symbolic execution.  The return value
    of fn is ignored because it may have many return values."""

    # XXX We could avoid this fork if we were smarter about cleaning
    # up all but the first code path
    # XXX Return a list of return values of fn.
    child = os.fork()
    if child == 0:
        try:
            fn(*args)
        except SystemExit:
            raise
        except:
            import traceback
            print >>sys.stderr, "Traceback (most recent call last):"
            etype, value, tb = sys.exc_info()
            traceback.print_tb(tb)
            state = str_state()
            if state is not None:
                print >>sys.stderr, "  If %s" % state.replace("\n", "\n" + " "*5)
            lines = traceback.format_exception_only(etype, value)
            for line in lines:
                sys.stderr.write(line)
        sys.exit(0)
    os.waitpid(child, 0)

#
# Utilities
#

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__
