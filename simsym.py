"""Simple symbolic execution engine for Python."""

import sys
import os
import z3
import types
import collections

# Monkey-patch __nonzero__ on Z3 types to make sure we don't
# accidentally call it instead of our wrappers.
def z3_nonzero(self):
    raise RuntimeError("Cannot __nonzero__ a %s" % self.__class__)
z3.ExprRef.__nonzero__ = z3_nonzero
del z3_nonzero

# Patch in a __hash__ for SortRef, to make it possible to put
# sorts as dictionary keys.
def z3_sort_hash(self):
    return hash(str(self))
z3.SortRef.__hash__ = z3_sort_hash
del z3_sort_hash

anon_idx = 0
def anon_name(base = "anon"):
    global anon_idx
    anon_idx += 1
    return "%s%d" % (base, anon_idx)

class Symbolic(object):
    """Base class of symbolic types.  Symbolic types come in two
    groups: constant and mutable.  Symbolic constants are deeply
    immutable.  Generally they are primitive types, such as integers
    and booleans, but more complex types can also be constants (e.g.,
    an immutable symbolic tuple of constants).  Mutable symbolic
    values are used for compound and container types like maps and
    structs.  Mutable values act like lvalues except when assigned,
    where they are copied at the point of assignment.

    A subclass of Symbolic must have a __z3_sort__ class field giving
    the z3.SortRef for the value's type.  Subclasses must also
    implement the _z3_value and _wrap_lvalue methods."""

    def __init__(self):
        raise RuntimeError("%s cannot be constructed directly" % strtype(self))

    @classmethod
    def _z3_sort(cls):
        """Return the Z3 sort of objects represented by this class."""
        return cls.__z3_sort__

    def _z3_value(self):
        """Return the Z3 value wrapped by this object.  For mutable
        objects, this should be its current value."""
        raise NotImplementedError("_z3_value is abstract")

    @classmethod
    def _new_lvalue(cls, init):
        """Return a new instance of Symbolic with the given initial
        value, which must be a Z3 value.  The returned instance's
        state will not be shared with any existing instances."""
        val = [init]
        def setter(nval):
            val[0] = nval
        obj = cls._wrap_lvalue(lambda: val[0], setter)
        assume(cls._assumptions(obj))
        return obj

    @classmethod
    def _wrap_lvalue(cls, getter, setter):
        """Create an instance of this object wrapping the Z3 value
        returned by getter.  If this object is immutable, then it
        should call getter immediately to fetch the object's current
        value.  If this object is mutable, it should use getter on
        demand and it should reflect changes to its value by calling
        setter with its updated Z3 value."""
        raise NotImplementedError("_wrap_lvalue is abstract")

    @classmethod
    def any(cls, name=None):
        """Return a symbolic value whose concrete value is unknown."""
        if name is None:
            name = anon_name()
        return cls._new_lvalue(z3.Const(name, cls._z3_sort()))

    @classmethod
    def _assumptions(cls, obj):
        """Return the assumptions that should apply to a fresh created
        lvalue of 'obj'."""
        # XXX Do we still need this?
        return obj.init_assumptions()

    def init_assumptions(self):
        return wrap(z3.BoolVal(True))

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return symnot(r)

class SymbolicConst(Symbolic):
    """The base class for symbolic constants.  Symbolic constants are
    deeply immutable values such as primitive types."""

    @classmethod
    def any(cls, name=None):
        # Const returns the most specific z3.*Ref type it can based on
        # the sort.  This is equivalent to Symbolic.any, but jumps
        # through fewer hoops.
        if name is None:
            name = anon_name()
        return cls._wrap(z3.Const(name, cls._z3_sort()))

    @classmethod
    def _wrap_lvalue(cls, getter, setter):
        # Fetch the value immediately, rather than acting like an
        # lvalue.
        return cls._wrap(getter())

#
# Z3 wrappers
#

# We construct a type hierarchy that parallels Z3's expression type
# hierarchy.  Each type wraps the equivalent Z3 type and defers to the
# Z3 methods for all symbolic operations (unwrapping the arguments and
# re-wrapping the results).  However, these types add methods specific
# to symbolic execution; most notably __nonzero__.  The leaves of this
# type hierarchy also provide Python types corresponding to Z3 sorts
# that we care about.

class MetaZ3Wrapper(type):
    """Metaclass to generate wrappers for Z3 ref object methods.

    The class must have a __ref_type__ field giving the Z3 ref type
    wrapped by the class.  The class may optionally have a
    __pass_type__ field, giving a Python type or tuple or types that
    should be passed through wrap untouched.

    The class must also have a __wrap__ field giving a list of method
    names to wrap.  For each method in __wrap__, the generated class
    will have a corresponding method with the same signature that
    unwraps all arguments, calls the Z3 method, and re-wraps the
    result.
    """

    def __new__(cls, classname, bases, classdict):
        if "__wrap__" in classdict:
            ref_type = classdict["__ref_type__"]
            for method in classdict.pop("__wrap__"):
                base_method = getattr(ref_type, method)
                nargs = base_method.__func__.__code__.co_argcount
                args = ["o%d" % i for i in range(nargs - 1)]
                code = "def %s(%s):\n" % (method, ",".join(["self"] + args))
                for o in args:
                    code += " if isinstance(%s, Symbolic): %s=%s._v\n" % \
                        (o, o, o)
                code += " return wrap(self._v.%s(%s))" % (method, ",".join(args))
                locals_dict = {}
                exec code in globals(), locals_dict
                classdict[method] = locals_dict[method]

        return type.__new__(cls, classname, bases, classdict)

    def _wrap(cls, z3ref):
        """Construct an instance of 'cls' wrapping the given Z3 ref
        object."""

        if not isinstance(z3ref, cls.__ref_type__):
            if hasattr(cls, "__pass_type__") and \
               isinstance(z3ref, cls.__pass_type__):
                return z3ref
            raise TypeError("%s expected %s, got %s" %
                            (cls.__name__, cls.__ref_type__.__name__,
                             strtype(z3ref)))
        obj = cls.__new__(cls)
        obj._v = z3ref
        return obj

class SExpr(Symbolic):
    __metaclass__ = MetaZ3Wrapper
    __ref_type__ = z3.ExprRef
    __wrap__ = ["__eq__", "__ne__"]

    def __str__(self):
        return str(self._v)

    def __repr__(self):
        return repr(self._v)

    def _z3_value(self):
        return self._v

class SArith(SExpr):
    __ref_type__ = z3.ArithRef
    __wrap__ = ["__add__", "__div__", "__mod__", "__mul__", "__pow__",
                "__sub__", "__truediv__",
                "__radd__", "__rdiv__", "__rmod__", "__rmul__", "__rpow__",
                "__rsub__", "__rtruediv__",
                "__ge__", "__gt__", "__le__", "__lt__",
                "__neg__", "__pos__"]

class SInt(SArith, SymbolicConst):
    __pass_type__ = int
    __z3_sort__ = z3.IntSort()

    # We're still wrapping ArithRef here (not IntNumRef).  This class
    # exists separately from SArith so we have Python type to parallel
    # Z3's int sort.  wrap will use this for any integral expression.

class UncheckableConstraintError(RuntimeError):
    def __init__(self, expr, reason):
        RuntimeError.__init__(
            self, 'Uncheckable constraint %s:\n%s' % (reason, z3.simplify(expr)))

class UnsatisfiablePath(RuntimeError):
    pass

class SBool(SExpr, SymbolicConst):
    __ref_type__ = z3.BoolRef
    __pass_type__ = bool
    __z3_sort__ = z3.BoolSort()

    def __nonzero__(self):
        solver = get_solver()

        global cursched, curschedidx
        if len(cursched) == curschedidx:
            # We've reached the end of replay; extend the schedule
            solver.push()
            solver.add(self._v)
            canTrue = solver.check()
            canTrueReason = solver.reason_unknown()
            if canTrue == z3.unknown:
                # Stack operations change how Z3 "compiles" formulas,
                # so it's possible it can solve it in isolation.
                s2 = z3.Solver()
                s2.add(*solver.assertions())
                canTrue = s2.check()
                canTrueReason = s2.reason_unknown()
            solver.pop()

            solver.push()
            solver.add(z3.Not(self._v))
            canFalse = solver.check()
            canFalseReason = solver.reason_unknown()
            if canFalse == z3.unknown:
                s2 = z3.Solver()
                s2.add(*solver.assertions())
                canFalse = s2.check()
                canFalseReason = s2.reason_unknown()
            solver.pop()

            if canTrue == z3.unsat and canFalse == z3.unsat:
                raise RuntimeError("Branch contradiction")

            # Extend the schedule
            if canTrue == z3.sat and canFalse == z3.unsat:
                cursched.append((True, cursched[-1][1]))
            elif canTrue == z3.unsat and canFalse == z3.sat:
                cursched.append((False, cursched[-1][1]))
            else:
                # Both are possible; take both paths
                gnode = cursched[-1][1]
                gnode.set_label(self, get_caller())
                tnode, fnode = curgraph.new_node(), curgraph.new_node()
                curgraph.new_edge(gnode, tnode, "T")
                curgraph.new_edge(gnode, fnode, "F")

                newsched = list(cursched)
                if canTrue == z3.sat:
                    cursched.append((True, tnode))
                else:
                    cursched.append((UncheckableConstraintError(
                                self._v, canTrueReason), tnode))
                if canFalse == z3.sat:
                    newsched.append((False, fnode))
                else:
                    newsched.append((UncheckableConstraintError(
                                z3.Not(self._v), canFalseReason), fnode))
                queue_schedule(newsched)

        # Follow the schedule (which we may have just extended)
        rv = cursched[curschedidx][0]
        if rv == True:
            solver.add(self._v)
        elif rv == False:
            solver.add(z3.Not(self._v))
        elif isinstance(rv, UncheckableConstraintError):
            raise rv
        else:
            raise RuntimeError("Bad schedule entry %r" % cursched[curschedidx])
        #assert solver.check() == z3.sat
        curschedidx = curschedidx + 1
        return rv

class SEnumBase(SExpr):
    __ref_type__ = z3.DatatypeRef

def tenum(name, vals):
    """Return a symbolic constant enumeration type called 'name' with
    the given values.  'vals' must be a list of strings or a string of
    space-separated names.  The returned type will have a class field
    corresponding to each concrete value and inherit from SEnumBase
    and SymbolicConst."""

    if isinstance(vals, basestring):
        vals = vals.split()
    sort, consts = z3.EnumSort(name, vals)
    fields = dict(zip(vals, consts))
    fields["__z3_sort__"] = sort
    return type(name, (SEnumBase, SymbolicConst), fields)

class STupleBase(SExpr):
    __ref_type__ = z3.DatatypeRef

def ttuple(name, *types):
    """Return a symbolic constant named tuple type with the given
    fields.  Each 'type' argument must be a pair of name and type.
    The returned type will inherit from STupleBase and SymbolicConst
    and will have properties for retrieving each component of the
    tuple."""

    sort = z3.Datatype(name)
    sort.declare(name, *[(fname, typ._z3_sort()) for fname, typ in types])
    sort = sort.create()
    fields = {"__z3_sort__" : sort}
    for fname, typ in types:
        code = """\
@property
def %s(self):
    return wrap(self.__z3_sort__.%s(self._v))""" % (fname, fname)
        locals_dict = {}
        exec code in globals(), locals_dict
        fields[fname] = locals_dict[fname]
    return type(name, (STupleBase, SymbolicConst), fields)

class SConstMapBase(SExpr):
    __ref_type__ = z3.ArrayRef
    __wrap__ = ["__getitem__"]

    @classmethod
    def constVal(cls, value):
        """Return a map where all keys map to 'value'."""
        return cls._wrap(z3.K(cls._z3_sort().domain(), unwrap(value)))

    def store(self, index, value):
        """Return a new map that is identical for this map except that
        'index' will map to 'value'."""
        return self._wrap(z3.Store(unwrap(self), unwrap(index), unwrap(value)))

def tconstmap(indexType, valueType):
    """Return an immutable map type (a z3 "array") that maps from
    symbolic constants of 'indexType' to symbolic constants of
    'valueType'.  The returned type will inherit from SConstMapBase
    and SymbolicConst."""

    sort = z3.ArraySort(indexType._z3_sort(), valueType._z3_sort())
    name = "SConstMap_%s_%s" % (indexType.__name__, valueType.__name__)
    return type(name, (SConstMapBase, SymbolicConst), {"__z3_sort__" : sort})

#
# Compound objects
#

class SMapBase(Symbolic):
    """The base type of symbolic mutable mapping types.  Objects of
    this type map from symbolic values to symbolic values.  Maps
    support slicing and slice assignment."""

    @classmethod
    def constVal(cls, value):
        """Return a map where all keys initially map to 'value'."""
        # XXX Should this simply be the role of __init__ in Symbolic
        # subclasses?
        return cls._new_lvalue(z3.K(cls._indexType._z3_sort(), unwrap(value)))

    @classmethod
    def _wrap_lvalue(cls, getter, setter):
        # XXX Make this generic?
        obj = cls.__new__(cls)
        obj._getter = getter
        obj._setter = setter
        return obj

    def _z3_value(self):
        # XXX Make this generic, too?
        return self._getter()

    @classmethod
    def _assumptions(cls, obj):
        x = cls._indexType.any()
        return symand([obj.init_assumptions(),
                       forall(x, cls._valueType._assumptions(obj[x]))])

    def __eq__(self, o):
        if not isinstance(o, SMapBase):
            return NotImplemented
        return wrap(self._getter() == o._getter())

    def __getitem__(self, idx):
        """Return the value at index 'idx'."""
        return self._valueType._wrap_lvalue(
            lambda: z3.Select(self._getter(), unwrap(idx)),
            lambda val: self.__setitem__(idx, val))

    def __setitem__(self, idx, val):
        """Change the value at index 'idx'."""
        self._setter(z3.Store(self._getter(), unwrap(idx), unwrap(val)))

def tmap(indexType, valueType):
    """Return a subclass of SMapBase that maps from 'indexType' to
    'valueType', where both must be subclasses of Symbolic."""
    # XXX We could accept a size and check indexes if indexType is an
    # ordered sort
    name = "SMap_%s_%s" % (indexType.__name__, valueType.__name__)
    sort = z3.ArraySort(indexType._z3_sort(), valueType._z3_sort())
    return type(name, (SMapBase,),
                {"_indexType" : indexType, "_valueType" : valueType,
                 "__z3_sort__" : sort})

class SStructBase(Symbolic):
    """The base type of symbolic mutable structure types.  Structure
    types have a fixed set of named fields, where the fields may have
    different symbolic types."""

    @classmethod
    def constVal(cls, __name=None, **fields):
        """Return a struct instance with specified field values.  Any
        fields omitted from 'fields' will be unspecified.  If any
        fields are omitted, the first positional argument must be
        supplied to name the symbolic constants for the omitted
        fields."""

        fvals = []
        for fname, typ in cls._fieldList:
            if fname in fields:
                fvals.append(unwrap(fields.pop(fname)))
            else:
                if __name is None:
                    raise ValueError(
                        "Name required for partially symbolic struct")
                fvals.append(unwrap(typ.any(__name + "." + fname)))
        if fields:
            raise AttributeError("Unknown struct field %r" % fields.keys()[0])
        return cls._new_lvalue(cls._ctor(*fvals))

    @classmethod
    def _wrap_lvalue(cls, getter, setter):
        obj = cls.__new__(cls)
        # Don't go through the overridden __setattr__.
        object.__setattr__(obj, "_getter", getter)
        object.__setattr__(obj, "_setter", setter)
        return obj

    def _z3_value(self):
        return self._getter()

    def _update(self, name, val):
        """Return a Z3 expression representing this struct with field
        'name' updated to Z3 value 'val'."""
        fvals = []
        for fname, _ in self._fieldList:
            if fname == name:
                fvals.append(unwrap(val))
            else:
                fvals.append(unwrap(getattr(self, fname)))
        return self._ctor(*fvals)

    def __eq__(self, o):
        if not isinstance(o, SStructBase):
            return NotImplemented
        return wrap(self._getter() == o._getter())

    def __getattr__(self, name):
        if name not in self._fields:
            raise AttributeError(name)
        fgetter = getattr(self.__z3_sort__, name)
        return self._fields[name]._wrap_lvalue(
            lambda: fgetter(self._getter()),
            lambda val: self.__setattr__(name, val))

    def __setattr__(self, name, val):
        self._setter(self._update(name, val))

def tstruct(**fields):
    """Return a subclass of SStructBase for a struct type with the
    given fields.  'fields' must be a dictionary mapping from names to
    symbolic types."""

    name = "SStruct_" + "_".join(fields.keys())
    z3name = anon_name(name)
    sort = z3.Datatype(z3name)
    fieldList = fields.items()
    sort.declare(z3name, *[(fname, typ._z3_sort()) for fname, typ in fieldList])
    sort = sort.create()

    type_fields = {"__slots__": [], "_fields": fields, "_fieldList": fieldList,
                   "_z3name": z3name, "__z3_sort__": sort,
                   "_ctor": getattr(sort, z3name)}
    return type(name, (SStructBase,), type_fields)

#
# Constructors
#

def symand(exprlist):
    if any([isinstance(x, Symbolic) for x in exprlist]):
        return wrap(z3.And([unwrap(x) for x in exprlist]))
    else:
        return all(exprlist)

def symor(exprlist):
    if any([isinstance(x, Symbolic) for x in exprlist]):
        return wrap(z3.Or([unwrap(x) for x in exprlist]))
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

def implies(a, b):
    return wrap(z3.Implies(unwrap(a), unwrap(b)))

def exists(vars, e, patterns=[]):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    return wrap(z3.Exists([unwrap(v) for v in vars], unwrap(e),
                          patterns=map(unwrap, patterns)))

def forall(vars, e, patterns=[]):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    return wrap(z3.ForAll([unwrap(v) for v in vars], unwrap(e),
                          patterns=map(unwrap, patterns)))

#
# Conversions to Z3 types and wrapper types
#

def unwrap(val):
    """Convert a value to a Z3 value.

    If val is a Symbolic, returns the wrapped Z3 value.
    Otherwise, simply returns val."""

    if isinstance(val, Symbolic):
        return val._z3_value()
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
        if ref.is_int():
            return SInt._wrap(ref)
        return SArith._wrap(ref)
    if isinstance(ref, z3.BoolRef):
        return SBool._wrap(ref)
    return SExpr._wrap(ref)

def wraplist(reflist):
    """Convert a list of values to a list of simsym.Symbolic things,
    by calling wrap() on each item in the list."""
    return [wrap(ref) for ref in reflist]

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
# Execution graph visualization
#

class Graph(object):
    def __init__(self):
        self.__nodes = []
        self.__edges = []

    def new_node(self):
        self.__nodes.append(GraphNode())
        return self.__nodes[-1]

    def new_edge(self, n1, n2, label):
        self.__edges.append((n1, n2, label))

    def show(self):
        import subprocess, tempfile
        with tempfile.NamedTemporaryFile(suffix=".pdf") as f:
            p = subprocess.Popen(["dot", "-Tpdf"], stdin=subprocess.PIPE,
                                 stdout=f)
            self.to_dot(p.stdin)
            p.stdin.close()
            p.wait()
            subprocess.check_call(["evince", f.name])

    def to_dot(self, fp=sys.stdout):
        print >>fp, "digraph G {"
        #print >>fp, "rankdir=LR;"
        for n in self.__nodes:
            print >>fp, "n%s [label=%s,color=%s,shape=box];" % \
                (id(n), self.__dot_quote(n.str_label()),
                 self.__dot_quote(n._color))
        for n1, n2, label in self.__edges:
            print >>fp, "n%s -> n%s [label=%s];" % \
                (id(n1), id(n2), self.__dot_quote(str(label)))
        print >>fp, "}"

    def __dot_quote(self, s):
        return '"' + (s.replace("\\", "\\\\")
                      .replace("\n", "\\l")
                      .replace("\"", "\\\"")) + '"'

class GraphNode(object):
    def __init__(self):
        self._label = ["?"]
        self._color = "black"

    def set_label(self, *parts):
        self._label = parts

    def set_color(self, color):
        self._color = color

    def str_label(self):
        res = []
        for part in self._label:
            if isinstance(part, Symbolic):
                res.append(str(z3.simplify(unwrap(part))))
            else:
                res.append(str(part))
        res = "\n".join(res).splitlines()
        if len(res) > 10:
            res = res[:5] + [".. %d more lines .." % (len(res) - 9)] + res[-4:]
        return "\n".join(res)

#
# Symbolic executor
#

solver = None
schedq = []
curgraph = None
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

def simplify(expr, try_harder=False):
    core_simplifier = 'ctx-simplify'
    if try_harder:
        ## ctx-solver-simplify is very slow; use the
        ## faster but less powerful ctx-simplify.
        core_simplifier = 'ctx-solver-simplify'
    t = z3.Repeat(z3.Then(z3.With('simplify', expand_select_store=True,
                                              ite_extra_rules=True,
                                              sort_eq=True,
                                              expand_store_eq=True),
                          'propagate-values',
                          'ctx-simplify',
                          core_simplifier,
                          ))
    subgoals = t(unwrap(expr))
    if len(subgoals[0]) == 0:
        s = wrap(z3.BoolVal(True))
    else:
        s = wrap(z3.simplify(unwrap(symand([symand(wraplist(g))
                                            for g in subgoals]))))
    return s

assume_list = []
def assume(e):
    """Declare symbolic expression e to be True."""

    global assume_list
    assume_list.append(e)

    if e is True:
        return

    # Is this assumption already implied?  This isn't strictly
    # necessary, but it cleans up generated expressions and the
    # execution graph.  It also sometimes lets z3 decide a path
    # condition that it otherwise can't (which is probably a z3 bug).
    solver = get_solver()
    solver.push()
    solver.add(unwrap(symnot(e)))
    sat = solver.check()
    solver.pop()
    if sat == z3.unsat:
        return

    # Update the schedule and execution graph.  (We wouldn't need to
    # track assumptions in the schedule except that we want to avoid
    # duplicate nodes in the execution graph.)
    global cursched, curschedidx
    if len(cursched) == curschedidx:
        if len(cursched):
            gnode = cursched[-1][1]
        else:
            gnode = curgraph.new_node()
        gnode.set_label(e, get_caller())
        nextnode = curgraph.new_node()
        curgraph.new_edge(gnode, nextnode, "")

        cursched.append((None, nextnode))

    assert cursched[curschedidx][0] is None
    curschedidx = curschedidx + 1

    solver.add(unwrap(e))
    sat = solver.check()
    if sat == z3.unknown:
        s2 = z3.Solver()
        s2.add(*solver.assertions())
        sat = s2.check()
        reason = s2.reason_unknown()

    if sat == z3.unsat:
        raise UnsatisfiablePath()
    elif sat != z3.sat:
        raise UncheckableConstraintError(unwrap(e), reason)

def symbolic_apply(fn, *args):
    """Evaluate fn(*args) under symbolic execution.  Return a map of
    return values to conditions under which that value is returned."""

    global curgraph
    curgraph = Graph()

    rvs = collections.defaultdict(list)
    # Prime the schedule with a root node.  We skip this during
    # execution, but it means we can always use graph node
    # cursched[-1][1].
    queue_schedule([(None, curgraph.new_node())])

    global schedq
    while len(schedq) > 0:
        global cursched
        cursched = schedq.pop()

        global curschedidx
        curschedidx = 1

        global solver
        solver = z3.Solver()
        try:
            rv = fn(*args)
            rvs[rv].append(symand(wraplist(solver.assertions())))
            cursched[-1][1].set_label(rv)
        except UnsatisfiablePath:
            cursched[-1][1].set_label("Unsatisfiable path")
            cursched[-1][1].set_color("blue")
        except UncheckableConstraintError as e:
            cursched[-1][1].set_label("Exception: " + str(e))
            cursched[-1][1].set_color("red")
            print str(e)
        except Exception as e:
            cursched[-1][1].set_label("Exception: " + str(e))
            cursched[-1][1].set_color("red")
            if len(e.args) == 1:
                e.args = ('%s in symbolic state:\n%s' % (e.args[0], str_state()),)
            else:
                e.args = e.args + (str_state(),)
            curgraph.show()
            raise
        finally:
            solver = None
#    curgraph.show()
    return rvs

def check(e):
    global solver
    clearsolver = False
    if solver is None:
        solver = z3.Solver()
        clearsolver = True
    solver.push()
    solver.add(unwrap(e))
    c = solver.check()
    if c == z3.sat:
        m = solver.model()
    else:
        if c == z3.unknown:
            m = solver.reason_unknown()
        else:
            m = None
    solver.pop()
    if clearsolver:
        solver = None
    return (c, m)

#
# Helpers for tracking "internal" variables
#

internal_vars = {None: SInt.any('__dummy')}

def add_internal(v):
    internal_vars[str(v)] = v

def internals():
    return [v for _, v in internal_vars.iteritems()]

#
# Utilities
#

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__

def get_caller():
    import inspect
    cur = inspect.currentframe()
    caller = inspect.getouterframes(cur, 3)
    return "%s:%s" % (os.path.basename(caller[2][1]), caller[2][2])
