"""Simple symbolic execution engine for Python."""

import sys
import os
import z3
import types
import collections

class _Region(object):
    """A mutable N-dimensional (where N may be 0) array of symbolic
    constants, indexed by N-tuples of symbolic constants.  Internally,
    all symbolic values are constructed via regions.  For individual
    constant values, the constructed region will be 0-dimensional.
    Compound types recursively break down into constant types and
    track separate regions for each contained constant type."""

    __slots__ = ["_dims", "_v", "_ctor"]

    def __init__(self, name, indexTypes, valueType, init=None):
        self._dims = len(indexTypes)
        if self._dims == 0:
            if init is None:
                self._v = z3.Const(name, valueType._z3_sort())
            else:
                self._v = init
            return

        if self._dims == 1:
            indexSort = indexTypes[0]._z3_sort()
        else:
            # Use a tuple type for the index
            if name is None:
                # XXX Make up a sort name?
                raise NotImplementedError("Multi-dimensional constant arrays")
            sname = name + ".idx"
            dt = z3.Datatype(sname)
            dt.declare(sname, *[("%s!%d" % (sname, i), typ._z3_sort())
                                for i, typ in enumerate(indexTypes)])
            indexSort = dt.create()
            self._ctor = getattr(indexSort, sname)

        if init is None:
            self._v = z3.Array(name, indexSort, valueType._z3_sort())
        else:
            self._v = z3.K(indexSort, unwrap(init))

    def select(self, idx):
        if len(idx) != self._dims:
            raise RuntimeError("Index length %d does not match dimensions %d" %
                               (len(idx), self._dims))
        if self._dims == 0:
            return wrap(self._v)
        elif self._dims == 1:
            return wrap(self._v[unwrap(idx[0])])
        else:
            return wrap(self._v[self._ctor(*map(unwrap, idx))])

    def store(self, idx, val):
        if len(idx) != self._dims:
            raise RuntimeError("Index length %d does not match dimensions %d" %
                               (len(idx), self._dims))
        if self._dims == 0:
            self._v = unwrap(val)
        elif self._dims == 1:
            self._v = z3.Store(self._v, unwrap(idx[0]), unwrap(val))
        else:
            self._v = z3.Store(self._v, self._ctor(*map(unwrap, idx)),
                               unwrap(val))

# Monkey-patch __nonzero__ on Z3 types to make sure we don't
# accidentally call it instead of our wrappers.
def z3_nonzero(self):
    raise RuntimeError("Cannot __nonzero__ a %s" % self.__class__)
z3.ExprRef.__nonzero__ = z3_nonzero
del z3_nonzero

anon_idx = 0
def anon_name():
    global anon_idx
    anon_idx += 1
    return 'anon%d' % anon_idx

class Symbolic(object):
    """Base class of symbolic types.  Symbolic types come in two
    groups: constant and mutable.  Symbolic constants are deeply
    immutable.  Generally they are primitive types, such as integers
    and booleans, but more complex types can also be constants (e.g.,
    an immutable symbolic tuple of constants).  Furthermore, types
    representing symbolic constants have a specific Z3 sort.  Mutable
    symbolic values are used for compound and container types like
    maps and structs.

    Subclasses must implement _make_region, _select, and
    _eq_region."""

    def __init__(self):
        raise RuntimeError("%s cannot be constructed directly" % strtype(self))

    @classmethod
    def _z3_sort(cls):
        """Return the Z3 sort represented by this class or raise an
        exception if this class does not represent symbolic
        constants."""
        raise TypeError("%s is symbolic, but not constant" % strtype(cls))

    @classmethod
    def any(cls, name=None):
        """Return a symbolic value whose concrete value is unknown."""
        if name is None:
            name = anon_name()
        obj = cls._select(cls._make_region(name, (), None), ())
        assume(cls._assumptions(obj))
        return obj

    @classmethod
    def _make_region(cls, name, indexTypes, init):
        """Construct a region or regions for storing an instance of
        this type.  Compound and collection types should recursively
        call the _make_region methods of their component types.
        'name' is the name given to this object; for compound types,
        the names of subregions must be derived from 'name'.
        'indexTypes' is the tuple of index types used to reach this
        object; for collection types, the index of the subregion must
        be an extension of 'indexTypes'.  'init', if not None, must be
        an instance of 'cls' or convertible to it and will be used as
        the initial value of the region.  The value returned by this
        method is opaque to the caller (it need not be an instance of
        _Region) and will be passed back to the _select method to
        retrieve values."""
        raise NotImplementedError("_make_region is abstract")

    @classmethod
    def _select(cls, region, index):
        """Return the value at 'index' of 'region'.  'region' will be
        a value returned by 'cls's _make_region method.  For compound
        and collection types, this should recursively select
        components from the compound's component types."""
        raise NotImplementedError("_select is abstract")

    @classmethod
    def _assumptions(cls, obj):
        """Return the assumptions for 'obj' returned by _select."""
        return obj.init_assumptions()

    def init_assumptions(self):
        return wrap(z3.BoolVal(True))

    @classmethod
    def _eq_region(cls, r1, r2):
        """Return a SBool that is True if r1 and r2 are equal, where
        r1 and r2 are value returned by _make_region."""
        raise NotImplementedError("_eq_region is abstract")

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return symnot(r)

class SymbolicConst(Symbolic):
    """The base class for symbolic constants.  Symbolic constants are
    deeply immutable values such as primitive types.  A subclass of
    SymbolicConst must have a __z3_sort__ class field giving the
    z3.SortRef for the value's type."""

    @classmethod
    def _z3_sort(cls):
        return cls.__z3_sort__

    @classmethod
    def any(cls, name=None):
        # Const returns the most specific z3.*Ref type it can based on
        # the sort.  This is equivalent to Symbolic.any, but jumps
        # through fewer hoops.
        if name is None:
            name = anon_name()
        return cls._wrap(z3.Const(name, cls._z3_sort()))

    @classmethod
    def _make_region(cls, name, indexTypes, init):
        return _Region(name, indexTypes, cls, init)

    @classmethod
    def _select(cls, region, idx):
        return region.select(idx)

    @staticmethod
    def _store(region, idx, val):
        region.store(idx, val)

    @classmethod
    def _eq_region(cls, r1, r2):
        return wrap(r1._v == r2._v)

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
    """Metaclass to generate wrappers for Z3 ref object methods.  The
    class should have a __ref_type__ field giving the Z3 ref type
    wrapped by the class, and __wrap__ field giving a list of method
    names to wrap.  For each method in __wrap__, the generated class
    will have a corresponding method with the same signature that
    unwraps all arguments, calls the Z3 method, and re-wraps the
    result."""

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

class SArith(SExpr):
    __ref_type__ = z3.ArithRef
    __wrap__ = ["__add__", "__div__", "__mod__", "__mul__", "__pow__",
                "__sub__", "__truediv__",
                "__radd__", "__rdiv__", "__rmod__", "__rmul__", "__rpow__",
                "__rsub__", "__rtruediv__",
                "__ge__", "__gt__", "__le__", "__lt__",
                "__neg__", "__pos__"]

class SInt(SArith, SymbolicConst):
    __z3_sort__ = z3.IntSort()

    # We're still wrapping ArithRef here (not IntNumRef).  This class
    # exists separately from SArith so we have Python type to parallel
    # Z3's int sort.  wrap will use this for any integral expression.

class UncheckableConstraintError(RuntimeError):
    def __init__(self, expr, reason):
        RuntimeError.__init__(
            self, 'Uncheckable constraint %s:\n%s' % (reason, z3.simplify(expr)))

class SBool(SExpr, SymbolicConst):
    __ref_type__ = z3.BoolRef
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
            solver.pop()

            solver.push()
            solver.add(z3.Not(self._v))
            canFalse = solver.check()
            canFalseReason = solver.reason_unknown()
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
    this type map from symbolic constants to symbolic values (constant
    or mutable).  Maps support slicing and slice assignment."""

    @classmethod
    def constVal(cls, value):
        """Return a map where all keys initially map to 'value'."""
        # XXX Should this simply be the role of __init__ in Symbolic
        # subclasses?
        return cls._select(cls._valueType._make_region(
                None, (cls._indexType,), value), ())

    @classmethod
    def _make_region(cls, name, indexTypes, init):
        if init is not None:
            if indexTypes == () and init._idx == ():
                return init._sub
            # XXX Ugh, what a mess.  With tuple-indexed regions,
            # there's no easy way to express this.  This and the
            # equality mess and the problem of naming region index
            # tuples suggests we should use nested array regions
            # instead.
            raise NotImplementedError("Initialized SMapBase._make_region")
        return cls._valueType._make_region(
            name, indexTypes + (cls._indexType,), None)

    @classmethod
    def _select(cls, subregion, idx):
        obj = cls.__new__(cls)
        obj._sub = subregion
        obj._idx = idx
        return obj

    @classmethod
    def _assumptions(cls, obj):
        x = cls._indexType.any()
        return symand([obj.init_assumptions(),
                       forall(x, cls._valueType._assumptions(obj[x]))])

    @classmethod
    def _eq_region(cls, s1, s2):
        return cls._valueType._eq_region(s1, s2)

    def __eq__(self, o):
        if not isinstance(o, SMapBase):
            return NotImplemented
        if type(self) != type(o):
            # Don't simply return NotImplemented or Python == will
            # return False, masking bugs.
            raise TypeError("Cannot compare incompatible map types %s and %s"%
                            (strtype(self), strtype(o)))
        if self._idx == () and o._idx == ():
            return self._eq_region(self._sub, o._sub)
        # Because we use tuple indexing, we need to explicitly
        # quantify over the free dimensions (in the special case
        # above, Z3 does this internally).  If higher-dimensional
        # regions were implemented with nested arrays, we could do
        # something more natural here.
        x = self._indexType.any()
        return forall(x, self[x] == o[x])

    def __getitem__(self, idx):
        """Return the value at index 'idx'."""
        return self._valueType._select(self._sub, self._idx + (idx,))

    def __setitem__(self, idx, val):
        """Change the value at index 'idx'.  'val' must be a primitive
        type; compound values cannot be assigned."""
        # We can only assign if the value type is a primitive type,
        # since we can't emulate reference semantics for compound
        # types (but value and reference semantics converge for
        # primitive types).
        # XXX Rename PrimitiveVal or something?
        if not issubclass(self._valueType, SymbolicConst):
            raise TypeError("%s does not support item assignment" %
                            strtype(self))
        self._valueType._store(self._sub, self._idx + (idx,), val)

def tmap(indexType, valueType):
    """Return a subclass of SMapBase that maps from 'indexType' to
    'valueType'.  'indexType' must be a symbolic constant type, but
    'valueType' can be any symbolic type."""

    # XXX We could accept a size and check indexes if indexType is an
    # ordered sort
    name = "SMap_%s_%s" % (indexType.__name__, valueType.__name__)
    return type(name, (SMapBase,), {"_indexType" : indexType,
                                    "_valueType" : valueType})

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

        init = {fname: None for fname in cls._fields}
        for fname, fval in fields.items():
            if fname not in init:
                raise AttributeError("Unknown struct field %r" % fname)
            init[fname] = fval
        if __name is None and any(init[fname] is None for fname in cls._fields):
            raise ValueError("Name required for partially specified struct")
        return cls._select(cls._make_region(__name, (), init), ())

    @classmethod
    def _make_region(cls, name, indexTypes, init):
        # init may be either a struct instance or a field dictionary.
        # Normalize it to a field dictionary.
        if isinstance(init, cls):
            init = {fname: getattr(init, fname) for fname in cls._fields}
        subregions = {}
        for fname, ftyp in cls._fields.items():
            subregions[fname] = ftyp._make_region(
                None if name is None else name + "." + fname, indexTypes,
                None if init is None else init[fname])
        return subregions

    @classmethod
    def _select(cls, subregions, idx):
        obj = cls.__new__(cls)
        # Don't go through the overridden __setattr__.
        object.__setattr__(obj, "_subregions", subregions)
        object.__setattr__(obj, "_idx", idx)
        return obj

    @classmethod
    def _assumptions(cls, obj):
        return symand([obj.init_assumptions()] +
                      [ftyp._assumptions(obj.__getattr__(fname))
                       for fname, ftyp in cls._fields.items()])

    @classmethod
    def _eq_region(cls, sr1, sr2):
        return symand([ftyp._eq_region(sr1[fname], sr2[fname])
                       for fname, ftyp in cls._fields.items()])

    def __eq__(self, o):
        if not isinstance(o, SStructBase):
            return NotImplemented
        if type(self) != type(o):
            # Don't simply return NotImplemented or Python == will
            # return False, masking bugs.
            raise TypeError("Cannot compare incompatible struct types %s and %s"%
                            (strtype(self), strtype(o)))
        if self._idx == () and o._idx == ():
            return self._eq_region(self._subregions, o._subregions)
        return symand([getattr(self, fname) == getattr(o, fname)
                       for fname in self._fields])

    def __getattr__(self, name):
        if name not in self._fields:
            raise AttributeError(name)
        return self._fields[name]._select(self._subregions[name], self._idx)

    def __setattr__(self, name, val):
        if name not in self._fields:
            raise AttributeError(name)
        if not issubclass(self._fields[name], SymbolicConst):
            raise TypeError("%s does not support item assignment" %
                            strtype(self))
        self._fields[name]._store(self._subregions[name], self._idx, val)

def tstruct(**fields):
    """Return a subclass of SStructBase for a struct type with the
    given fields.  'fields' must be a dictionary mapping from names to
    symbolic types."""

    name = "SStruct_" + "_".join(fields.keys())
    type_fields = {"__slots__": [], "_fields": fields}
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

def exists(vars, e):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    return wrap(z3.Exists([unwrap(v) for v in vars], unwrap(e)))

def forall(vars, e):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    return wrap(z3.ForAll([unwrap(v) for v in vars], unwrap(e)))

#
# Conversions to Z3 types and wrapper types
#

def unwrap(val):
    """Convert a value to a Z3 value.

    If val is a simsym.SExpr, returns the wrapped Z3 value.
    Otherwise, simply returns val."""

    if isinstance(val, SExpr):
        return val._v
    if isinstance(val, Symbolic):
        raise TypeError("Can't unwrap %r; no corresponding Z3 value" % val)
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
            print >>fp, "n%s [label=%s,shape=box];" % \
                (id(n), self.__dot_quote(n.str_label()))
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

    def set_label(self, *parts):
        self._label = parts

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

def simplify(expr):
    t = z3.Repeat(z3.Then('propagate-values',
                          ## ctx-solver-simplify is very slow; use the
                          ## faster but less powerful ctx-simplify.
                          'ctx-simplify',
                          z3.With('simplify', expand_select_store=True)))
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
    if sat == z3.unsat:
        raise RuntimeError("Unsatisfiable assumption %s" % e)
    elif sat != z3.sat:
        raise RuntimeError("Uncheckable assumption %s" % e)

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
        except UncheckableConstraintError as e:
            cursched[-1][1].set_label("Exception: " + str(e))
            print str(e)
        except Exception as e:
            cursched[-1][1].set_label("Exception: " + str(e))
            if len(e.args) == 1:
                e.args = ('%s in symbolic state:\n%s' % (e.args[0], str_state()),)
            else:
                e.args = e.args + (str_state(),)
            curgraph.show()
            raise
        finally:
            solver = None
#    curgraph.show()
    return { val: symor(condlist) for val, condlist in rvs.items() }

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
