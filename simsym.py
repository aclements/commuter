"""Simple symbolic execution engine for Python."""

import sys
import os
import z3
import types
import collections
import inspect
import graph

class options(object):
    # If set, equality tests eagerly simplify expressions that are
    # structurally identical to a concrete True.  This can produce
    # much simpler equality expressions, especially when comparing
    # large structures, but can sometimes turn what looks like a
    # symbolic branch into a concrete branch, which can be confusing
    # when tracing symbolic execution.
    eq_eliminate_structural = True

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

anon_info = ""
def gen_name(template=None):
    """Generate a variable name from a template.

    If the template is None or ends with *, this generates a fresh
    anonymous name containing the template before the *, the value of
    anon_info, and a nonce.
    """

    if template is None:
        template = "*"
    if template.endswith("*"):
        name = "%s%s_anon%d" % (template[:-1], anon_info, Env.current().anon_idx)
        Env.current().anon_idx += 1
        return name
    return template

class Constant(object):
    def __init__(self, name):
        self.__name = name

    def __repr__(self):
        return __name__ + "." + self.__name

MODEL_FETCH = Constant("MODEL_FETCH")

REALM_IGNORE = Constant("REALM_IGNORE")

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
    the compound z3.SortRef for the value's type.  Subclasses must
    also implement the _z3_value and _wrap_lvalue methods.
    """

    def __init__(self):
        raise RuntimeError("%s cannot be constructed directly" % strtype(self))

    @classmethod
    def _z3_sort(cls):
        """Return the compound Z3 sort represented by this class."""
        return cls.__z3_sort__

    def _z3_value(self):
        """Return the compound Z3 value wrapped by this object.

        For mutable objects, this should be its current value.
        """
        raise NotImplementedError("_z3_value is abstract")

    @classmethod
    def _new_lvalue(cls, init, model):
        """Return a new instance of Symbolic with the given initial value,
        which must be a compound Z3 value.  The returned instance's
        state will not be shared with any existing instances.  model,
        if not None, provides the simsym.Model in which to evaluate
        concrete values or MODEL_FETCH to retrieve an existing
        variable without binding it to a model.
        """
        val = [init]
        def setter(nval):
            val[0] = nval
        obj = cls._wrap_lvalue(lambda: val[0], setter, model)
        if model is None and isinstance(obj, Symbolic):
            obj._declare_assumptions(assume)
        return obj

    @classmethod
    def _wrap_lvalue(cls, getter, setter, model):
        """Return a new instance of this class.

        Return an instance of this class wrapping the compound Z3
        value returned by getter.  If this object is immutable, then
        it should call getter immediately to fetch the object's
        current value.  If this object is mutable, it should use
        getter on demand and it should reflect changes to its value by
        calling setter with its updated compound Z3 value.

        model, if not None, provides the simsym.Model in which to
        evaluate concrete values or is MODEL_FETCH.  Immutable,
        non-compound objects should use this to evaluate their
        concrete Python value and return this concrete value.
        Mutable, compound objects should pass this model down to their
        components.
        """
        raise NotImplementedError("_wrap_lvalue is abstract")

    @classmethod
    def var(cls, name=None, model=None):
        """Return a symbolic variable of this type.

        Initially, the variable's value will be unconstrained.  It may
        become constrained or even concrete as the program progresses.

        If this method is called multiple times with the same name,
        the returned instances will represent the same underlying
        symbolic value (though the instances themselves will be
        distinct).

        If model is provided, it must be a simsym.Model or
        MODEL_FETCH.  If it is a Model, this symbolic variable will be
        interpreted in this model to get a concrete Python value.  If
        it is MODEL_FETCH, a variable equivalent to the initial value
        of the variable of the given name will be returned, but not
        bound in any model.
        """

        name = gen_name(name)
        if model is None:
            Env.current().var_constructors[name] = cls.var
        def mkValue(path, sort):
            if isinstance(sort, dict):
                return {k: mkValue(path + (k,), v)
                        for k, v in sort.iteritems()}
            strname = ".".join((name,) + path)
            # Record the simsym type of this constant
            Env.current().const_types[strname] = (cls, path)
            # Create the Z3 constant
            return z3.Const(strname, sort)
        return cls._new_lvalue(mkValue((), cls._z3_sort()), model)

    def _declare_assumptions(self, assume):
        """Declare assumptions for a new lvalue self.

        This is called for newly created lvalues and should be
        implemented by subclasses requiring assumption declarations.
        Implementations should call the argument 'assume' with boolean
        expressions involving self that must be true.  Usually
        'assume' is simply simsym.assume, but in situations involving
        extensional arrays (i.e., maps) it may bind quantifiers.

        Subclasses that override this method should always invoke the
        parent class' _declare_assumptions method.

        For compound types, since only the compound itself is a newly
        created lvalue, the implementation of _declare_assumptions
        should project the components of the compound and call each
        component's _declare_assumptions method.
        """
        pass

    def __eq__(self, o):
        if options.eq_eliminate_structural and self.eq(o):
            return True
        return self._eq_internal(o)

    def _eq_internal(self, o):
        """Abstract method for equality testing.

        In general, subclasses should override _eq_internal to
        implement equality testing, as __eq__ performs structural
        equality optimization before calling this.
        """
        raise NotImplementedError('_eq_internal is abstract')

    def __ne__(self, o):
        if options.eq_eliminate_structural and self.eq(o):
            return False
        return self._ne_internal(o)

    def _ne_internal(self, o):
        return symnot(self._eq_internal(o))

    def eq(self, o):
        """Return True if self and o are structurally identical.

        This is what Python's == would usually mean, but Symbolic
        overrides == to return symbolic equality expressions.
        """
        if self is o:
            return True
        if not isinstance(o, Symbolic):
            return False
        def rec(a, b):
            if isinstance(a, dict) != isinstance(b, dict):
                return False
            if isinstance(a, dict):
                if len(a) != len(b):
                    return False
                for k in a.keys():
                    if k not in b or not rec(a[k], b[k]):
                        return False
            elif z3.is_ast(a):
                return z3.is_ast(b) and a.eq(b)
            else:
                return a == b
        return rec(self._z3_value(), o._z3_value())

    def __hash__(self):
        return hash(compound_map(lambda val: val.hash(), self._z3_value()))

    def copy(self):
        """Return a deep copy of this object.

        For immutable values, this should be overridden to return
        self.
        """
        # Assumptions have already been declared on the underlying Z3
        # value, so don't assume them again
        return self.bind(MODEL_FETCH)

    def bind(self, model):
        """Return a deep copy of this object that is bound to model."""
        return self._new_lvalue(compound_map(lambda x:x, self._z3_value()),
                                model)

class SymbolicConst(Symbolic):
    """The base class for symbolic constants.  Symbolic constants are
    deeply immutable values such as primitive types."""

    @classmethod
    def var(cls, name=None, model=None):
        # Const returns the most specific z3.*Ref type it can based on
        # the sort.  This is equivalent to Symbolic.var, but jumps
        # through fewer hoops.
        name = gen_name(name)
        if model is None:
            Env.current().var_constructors[name] = cls.var
        Env.current().const_types[name] = (cls, ())
        return cls._wrap(z3.Const(name, cls._z3_sort()), model)

    @classmethod
    def _wrap_lvalue(cls, getter, setter, model):
        # Fetch the value immediately, rather than acting like an
        # lvalue.
        return cls._wrap(getter(), model)

    def copy(self):
        """Return a deep copy of this object.

        Since this is an immutable value, this returns self.
        """
        return self

#
# Compounds
#

# A "compound X" is either an X or a dictionary from component names
# (e.g., struct fields) to compound X's.

def compound_map(func, *compounds):
    if len(compounds) == 1:
        return compound_map1(func, compounds[0])
    else:
        return compound_mapN(func, compounds)

def compound_map1(func, compound):
    if isinstance(compound, dict):
        return {k: compound_map1(func, v) for k, v in compound.iteritems()}
    return func(compound)

def compound_mapN(func, compounds):
    if isinstance(compounds[0], dict):
        return {k: compound_mapN(func, [c[k] for c in compounds])
                for k in compounds[0].iterkeys()}
    return func(*compounds)

def flatten_compound(compound):
    """Return a list of compound's leafs.

    Note that the returned leafs are in no particular order and the
    order may even differ between flattenings of structurally
    equivalent compounds.
    """
    res = []
    def rec(compound):
        if isinstance(compound, dict):
            for sub in compound.itervalues():
                rec(sub)
        else:
            res.append(compound)
    rec(compound)
    return res

#
# Z3 wrappers
#

# Below, we construct Symbolic subclasses that parallel Z3 sorts.
# These are organized into a functional class hierarchy so that, for
# example, all sorts supporting arithmetic operations can share a
# superclass that wraps the arithmetic operations.  (These functional
# superclasses are not strictly abstract; because our wrapping of Z3
# sorts is not complete, we may wrap a Z3 expression using one of
# these superclasses if we don't know its specific sort.)  Most of the
# methods in these classes simply wrap underlying Z3 methods
# (unwrapping the arguments and re-wrapping the result).

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
            OVERRIDES = {"__eq__" : "_eq_internal",
                         "__ne__" : "_ne_internal"}
            ref_type = classdict["__ref_type__"]
            for method in classdict.pop("__wrap__"):
                base_method = getattr(ref_type, method)
                nargs = base_method.__func__.__code__.co_argcount
                args = ["o%d" % i for i in range(nargs - 1)]
                dmethod = OVERRIDES.get(method, method)
                code = "def %s(%s):\n" % (dmethod, ",".join(["self"] + args))
                for o in args:
                    code += " if isinstance(%s, Symbolic): %s=%s._v\n" % \
                        (o, o, o)
                code += " return wrap(self._v.%s(%s))" % (method, ",".join(args))
                locals_dict = {}
                exec code in globals(), locals_dict
                classdict[dmethod] = locals_dict[dmethod]

        return type.__new__(cls, classname, bases, classdict)

    def _wrap(cls, z3ref, model):
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
        obj._model = model
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

    def eval(self, realm=None):
        """The concrete value of this constant in the bound model.

        The concrete assignment of this constant will be recorded in
        the bound model.  realm specifies the assignment realm to
        record it under.  The default realm is None.  REALM_IGNORE is
        handled specially and will cause this assignment to not be
        recorded.
        """
        if self._model and self._model is not MODEL_FETCH:
            return self._model._eval(self, realm)
        raise ValueError("%s is not bound to a model" % self)

    @property
    def val(self):
        """The concrete value of this constant in the bound model.

        This will track the evaluation in the model so that over
        values can be enumerated by concolic execution.
        """
        return self.eval()

    @property
    def someval(self):
        """Some concrete value of this constant in the bound model.

        Unlike val, this does not track this evaluation in the model,
        so it will not cause concolic execution to try other values.
        """
        return self.eval(REALM_IGNORE)

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

    # Note that we're wrapping ArithRefs, not IntNumRefs.  Z3's Ref
    # hierarchy reflects AST structure, while our types reflect Z3
    # sorts (which Z3 can't do because its C implementation can't
    # construct new types on the fly like we can in Python).

class UncheckableConstraintError(RuntimeError):
    def __init__(self, expr, reason):
        RuntimeError.__init__(self, reason)
        self.expr = expr

class UnsatisfiablePath(RuntimeError):
    pass

class ReplayDivergedError(RuntimeError):
    def __init__(self, old, new):
        RuntimeError.__init__(
            self, 'Replay diverged\nOld: %s\nNew: %s' % (old, new))

class SBool(SExpr, SymbolicConst):
    __ref_type__ = z3.BoolRef
    __pass_type__ = bool
    __z3_sort__ = z3.BoolSort()

    def __nonzero__(self):
        if self._model and self._model is not MODEL_FETCH:
            return self.val

        scheduler, path_state = Env.scheduler(), Env.path_state()
        solver = path_state.solver
        cursched = path_state.sched

        if len(cursched) == path_state.schedidx:
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
                cursched.append(SchedNode("branch_det", self, True))
            elif canTrue == z3.unsat and canFalse == z3.sat:
                cursched.append(SchedNode("branch_det", self, False))
            else:
                # Both are possible (or at least one is unknown)
                newsched = list(cursched)
                if canTrue == z3.sat:
                    cursched.append(SchedNode("branch_nondet", self, True))
                elif canTrue == z3.unknown:
                    cursched.append(
                        SchedNode("exception", True,
                                  UncheckableConstraintError(
                                      self._v, canTrueReason)))
                else:
                    assert canTrue == z3.unsat and canFalse == z3.unknown
                    # There's actually only one way to go
                    newsched = cursched

                if canFalse == z3.sat:
                    newsched.append(SchedNode("branch_nondet", self, False))
                elif canFalse == z3.unknown:
                    newsched.append(
                        SchedNode("exception", False,
                                  UncheckableConstraintError(
                                      z3.Not(self._v), canFalseReason)))
                else:
                    assert canFalse == z3.unsat and canTrue == z3.unknown
                    newsched = cursched

                if newsched is not cursched:
                    scheduler.queue_schedule(newsched)
        else:
            # We're replaying; check that replay hasn't diverged
            node = cursched[path_state.schedidx]
            if node.is_branch() and not node.expr.eq(self):
                raise ReplayDivergedError(node.expr, self)

        # Follow the schedule (which we may have just extended)
        node = cursched[path_state.schedidx]
        path_state.schedidx += 1
        if node.is_branch():
            solver.add(unwrap(node.path_expr()))
            return node.val
        elif node.typ == "exception":
            raise node.val
        else:
            raise ReplayDivergedError(node, "branch")

class SUninterpretedBase(SExpr):
    pass

def tuninterpreted(name):
    """Return a new uninterpreted symbolic type.

    This type is inhabited by an unbounded number of distinct
    constants.
    """
    return type(name, (SUninterpretedBase, SymbolicConst),
                {"__z3_sort__": z3.DeclareSort(name)})

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

    # XXX Broken: synonym types, assumptions
    raise Exception("Sorry, ttuple is broken right now")

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
        return cls._wrap(z3.K(cls._z3_sort().domain(), unwrap(value)), None)

    def store(self, index, value):
        """Return a new map that is identical for this map except that
        'index' will map to 'value'."""
        return self._wrap(z3.Store(unwrap(self), unwrap(index), unwrap(value)),
                          None)

def tconstmap(indexType, valueType):
    """Return an immutable map type (a z3 "array") that maps from
    symbolic constants of 'indexType' to symbolic constants of
    'valueType'.  The returned type will inherit from SConstMapBase
    and SymbolicConst."""

    sort = z3.ArraySort(indexType._z3_sort(), valueType._z3_sort())
    name = "SConstMap_%s_%s" % (indexType.__name__, valueType.__name__)
    return type(name, (SConstMapBase, SymbolicConst), {"__z3_sort__" : sort})

#
# Type synonyms
#

def tsynonym(name, baseType):
    """Return a new type that's equivalent to baseType."""
    return type(name, (baseType,), {})

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
        indexSort = cls._indexType._z3_sort()
        return cls._new_lvalue(
            compound_map(lambda val: z3.K(indexSort, val), unwrap(value)),
            None)

    @classmethod
    def _wrap_lvalue(cls, getter, setter, model):
        # XXX Make this generic?
        obj = cls.__new__(cls)
        obj._getter = getter
        obj._setter = setter
        obj._model = model
        return obj

    def _z3_value(self):
        # XXX Make this generic, too?
        return self._getter()

    def _declare_assumptions(self, assume):
        super(SMapBase, self)._declare_assumptions(assume)
        x = self._indexType.var()
        self[x]._declare_assumptions(lambda expr: assume(forall(x, expr)))

    def _eq_internal(self, o):
        if type(self) != type(o):
            return NotImplemented
        if isinstance(self._valueType, SExpr):
            # Optimize away the forall
            vs, vo = self._getter(), o._getter()
            assert not isinstance(vs, dict)
            assert not isinstance(vo, dict)
            return wrap(vs == vo)
        # valueType may have a complex __eq__.  In many (all?) cases
        # the forall isn't actually necessary, but we don't have the
        # mechanism to push it down the AST and eliminate it.
        x = self._indexType.var()
        return forall(x, self[x] == o[x])

    def __getitem__(self, idx):
        """Return the value at index 'idx'."""
        z3idx = unwrap(idx)
        return self._valueType._wrap_lvalue(
            lambda: compound_map(
                lambda z3val: z3.Select(z3val, z3idx), self._getter()),
            lambda val: self.__setitem__(idx, val),
            self._model)

    def __setitem__(self, idx, val):
        """Change the value at index 'idx'."""
        z3idx = unwrap(idx)
        def set1(z3map, z3val):
            # If we have an array of structs, assigning to a single
            # struct field will cause an identity update of all of the
            # other fields.  Avoid building up huge, pointless Store
            # expressions.
            if z3.is_ast(z3val) and z3map[z3idx].eq(z3val):
                return z3map
            return z3.Store(z3map, z3idx, z3val)
        self._setter(compound_map(set1, self._getter(), unwrap(val)))

def tmap(indexType, valueType):
    """Return a subclass of SMapBase that maps from 'indexType' to
    'valueType', where both must be subclasses of Symbolic."""
    # XXX We could accept a size and check indexes if indexType is an
    # ordered sort
    name = "SMap_%s_%s" % (indexType.__name__, valueType.__name__)

    indexSort = indexType._z3_sort()
    if isinstance(indexSort, dict):
        raise TypeError("Map index may not be a compound type")
    sort = compound_map(lambda z3sort: z3.ArraySort(indexSort, z3sort),
                        valueType._z3_sort())
    return type(name, (SMapBase,),
                {"_indexType" : indexType, "_valueType" : valueType,
                 "__z3_sort__" : sort})

class SStructBase(Symbolic):
    """The base type of symbolic mutable structure types.  Structure
    types have a fixed set of named fields, where the fields may have
    different symbolic types."""

    @classmethod
    def var(cls, __name=None, __model=None, **fields):
        """Return a struct instance with specified field values.

        Any fields omitted from 'fields' will be unspecified.  If no
        field values are provided, this is equivalent to Symbolic.var.
        """

        __name = gen_name(__name)
        if __model is None:
            # Field values may be mutable Symbolic values, but we want
            # to save their current value, so snapshot them by
            # unwrapping their values.
            fieldsSnapshot = {k: unwrap(v) for k,v in fields.items()}
            Env.current().var_constructors[__name] \
                = lambda _, model: cls.var(__name, model, **fieldsSnapshot)

        def mkValue(path, sort):
            if len(path) == 1 and path[0] in fields:
                return unwrap(fields.pop(path[0]))
            if isinstance(sort, dict):
                return {k: mkValue(path + (k,), v)
                        for k, v in sort.iteritems()}
            strname = ".".join((__name,) + path)
            # Record the simsym type of this constant
            Env.current().const_types[strname] = (cls, path)
            # Create the Z3 constant
            return z3.Const(strname, sort)
        z3_val = mkValue((), cls._z3_sort())
        if fields:
            raise AttributeError("Unknown struct field %r" % fields.keys()[0])
        return cls._new_lvalue(z3_val, __model)

    @classmethod
    def _wrap_lvalue(cls, getter, setter, model):
        obj = cls.__new__(cls)
        # Don't go through the overridden __setattr__.
        object.__setattr__(obj, "_getter", getter)
        object.__setattr__(obj, "_setter", setter)
        object.__setattr__(obj, "_model", model)
        return obj

    def _z3_value(self):
        return self._getter()

    def _declare_assumptions(self, assume):
        super(SStructBase, self)._declare_assumptions(assume)
        for fname in self._fields:
            sub = getattr(self, fname)
            if isinstance(sub, Symbolic):
                sub._declare_assumptions(assume)

    def _eq_internal(self, o):
        if type(self) != type(o):
            return NotImplemented
        return symand([getattr(self, name) == getattr(o, name)
                       for name in self._fields])

    def __getattr__(self, name):
        if name not in self._fields:
            raise AttributeError(name)
        return self._fields[name]._wrap_lvalue(
            lambda: self._getter()[name],
            lambda val: self.__setattr__(name, val),
            self._model)

    def __setattr__(self, name, val):
        if name not in self._fields:
            raise AttributeError(name)
        cval = self._getter()
        cval[name] = unwrap(val)
        self._setter(cval)

def tstruct(**fields):
    """Return a subclass of SStructBase for a struct type with the
    given fields.  'fields' must be a dictionary mapping from names to
    symbolic types."""

    name = "SStruct_" + "_".join(fields.keys())
    sort = {fname: typ._z3_sort() for fname, typ in fields.items()}
    type_fields = {"__slots__": [], "_fields": fields, "__z3_sort__": sort}
    return type(name, (SStructBase,), type_fields)

#
# Constructors
#

def symand(exprlist):
    # Remove concrete True values, short-circuit concrete False values
    nexprlist = []
    for x in exprlist:
        if isinstance(x, Symbolic):
            nexprlist.append(x)
        elif not x:
            return False
    if len(nexprlist):
        return wrap(z3.And([unwrap(x) for x in nexprlist]))
    return True

def symor(exprlist):
    # Remove concrete False values, short-circuit concrete True values
    nexprlist = []
    for x in exprlist:
        if isinstance(x, Symbolic):
            nexprlist.append(x)
        elif x:
            return True
    if len(nexprlist):
        return wrap(z3.Or([unwrap(x) for x in nexprlist]))
    return False

def symnot(e):
    if isinstance(e, Symbolic):
        return wrap(z3.Not(unwrap(e)))
    else:
        return not e

def symeq(*exprs):
    if len(exprs) == 2 and isinstance(exprs[0], tuple) \
       and isinstance(exprs[1], tuple):
        # XXX Do we still use this?
        a, b = exprs
        if len(a) != len(b):
            return False
        return symand([symeq(aa, bb) for (aa, bb) in zip(a, b)])
    if len(exprs) == 2:
        return exprs[0] == exprs[1]
    return symand([a == b for a, b in zip(exprs, exprs[1:])])

def symif(pred, cons, alt):
    return wrap(z3.If(unwrap(pred), unwrap(cons), unwrap(alt)))

def distinct(*exprlist):
    return wrap(z3.Distinct(*map(unwrap, exprlist)))

def implies(a, b):
    return wrap(z3.Implies(unwrap(a), unwrap(b)))

def exists(vars, e, patterns=[]):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    if not isinstance(e, (Symbolic, z3.ExprRef)):
        return e
    z3vars = []
    for v in vars:
        if isinstance(v, Symbolic):
            z3vars.extend(flatten_compound(v._z3_value()))
        elif isinstance(v, z3.ExprRef):
            z3vars.append(v)
        else:
            raise TypeError("exists variable must be symbolic")
    if len(z3vars) == 0:
        return e
    return wrap(z3.Exists(z3vars, unwrap(e), patterns=map(unwrap, patterns)))

def forall(vars, e, patterns=[]):
    if not isinstance(vars, (list, tuple)):
        vars = [vars]
    if not isinstance(e, (Symbolic, z3.ExprRef)):
        return e
    z3vars = []
    for v in vars:
        if isinstance(v, Symbolic):
            z3vars.extend(flatten_compound(v._z3_value()))
        elif isinstance(v, z3.ExprRef):
            z3vars.append(v)
        else:
            raise TypeError("forall variable must be symbolic")
    if len(z3vars) == 0:
        return e
    return wrap(z3.ForAll(z3vars, unwrap(e), patterns=map(unwrap, patterns)))

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

    # XXX It's probably not correct to always pass None for the model
    # below.  For example, in SMapBase.__eq__, we should probably pass
    # in the map's model.
    if isinstance(ref, z3.ArithRef):
        if ref.is_int():
            return SInt._wrap(ref, None)
        return SArith._wrap(ref, None)
    if isinstance(ref, z3.BoolRef):
        return SBool._wrap(ref, None)
    return SExpr._wrap(ref, None)

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

class SchedGraph(graph.Graph):
    def __init__(self):
        super(SchedGraph, self).__init__()
        self.node_attrs(shape="box")
        # SchedNodes are graph *edges*.  When the schedule forks,
        # we'll get two SchedNodes with identical metadata but
        # different vals.  For each graph node, we pick the first edge
        # out of it we see to represent that graph node and we
        # identify it by its predecessor SchedNode (which can be
        # thought of as the edge tail going in to the graph node).
        self.__tail_to_gnode = {}

    def add_sched(self, sched, result, result_color=None):
        prev_snode = None
        path = []
        for snode in sched:
            if snode.typ in ("assumption", "branch_nondet"):
                gnode = self.__tail_to_gnode.get(prev_snode)
                if gnode is None:
                    gnode = self.__tail_to_gnode[prev_snode] = self.node(snode)
                if snode.typ == "branch_nondet":
                    edge_attrs = {"label": str(snode.val)[0]}
                else:
                    edge_attrs = {}
                path.append((gnode, edge_attrs))
            prev_snode = snode
        path.append((self.node(result, unique=True, color=result_color), {}))
        for (n1, attrs), (n2, _) in zip(path, path[1:]):
            self.edge(n1, n2, **attrs)

    def obj_attrs(self, node):
        if isinstance(node, SchedNode):
            parts = []
            if node.expr is not None:
                parts.append(str(z3.simplify(unwrap(node.expr))))
            parts.append("%s:%s" % (os.path.basename(node.frames[0].filename),
                                    node.frames[0].lineno))
            label = "\n".join(parts)
        else:
            label = str(node)

        # Trim label
        if len(label.splitlines()) > 10:
            lines = label.splitlines()
            lines = lines[:5] + [".. %d more lines .." % (len(lines) - 9)] + lines[-4:]
            label = "\n".join(lines)
        return {"label": label}

#
# Symbolic executor
#

class Env(object):
    """Execution environment.

    An execution environment tracks symbolic declarations, the current
    scheduler, and the current path state.  Execution environments
    form a tree.  There is always a global execution environment, even
    when we're not performing symbolic execution, since symbolic
    declarations can occur anywhere.
    """

    def __init__(self, parent, scheduler=None, path_state=None):
        self.scheduler, self.path_state = scheduler, path_state

        # Map from user-provided Symbolic variable names to Symbolic
        # instance constructors.  Each instance constructor must take
        # two arguments: the user variable name and a simsym.Model
        # object that binds the Z3 environment.
        self.var_constructors = parent.var_constructors.copy() if parent else {}

        # Map from Z3 constant names to (outer Symbolic type, compound
        # path)
        self.const_types = parent.const_types.copy() if parent else {}

        # Anonymous variable index.  It's important that each code
        # path start with the same anonymous index to make replay
        # deterministic.  Otherwise, the replayed part of a schedule
        # may use one name for a variable, while the post-replay part
        # uses another.
        self.anon_idx = parent.anon_idx if parent else 0

    __current = None

    @classmethod
    def current(cls):
        """Return the current Env."""
        return cls.__current

    @classmethod
    def scheduler(cls):
        """Return the current Scheduler.

        Raise RuntimeError if no Scheduler is active."""
        if cls.__current.scheduler is None:
            raise RuntimeError("Symbolic execution attempted outside symbolic_apply")
        return cls.__current.scheduler

    @classmethod
    def path_state(cls):
        """Return the current PathState.

        Raise RuntimeError if no PathState is active."""
        if cls.__current.path_state is None:
            raise RuntimeError("Symbolic execution attempted outside symbolic_apply")
        return cls.__current.path_state

    def activate(self):
        """Make this environment current."""
        Env.__current = self
Env.global_env = Env(None)
Env.global_env.activate()

class SchedNode(object):
    """A node in the schedule graph.

    There are several types of nodes:

    - "branch_nondet" for a non-deterministic branch.  val must be
      True or False.

    - "branch_det" for a deterministic branch.  val must be True or
      False.  These are recorded for replay purposes; if we didn't
      record these, we would have to invoke the solver on every branch
      just to find out if we should consult the schedule.

    - "exception" for an UncheckableConstraintError.  expr must be
      True or False to indicate whether this was the true or false
      branch that was uncheckable.  val must be the exception to raise
      at this point in the schedule.  If an exception node appears in
      a schedule, it must be the last node.

    - "assumption" for an assumption.  val must be True.

    - "note" for a user-defined schedule note.  expr must be None.
      val must be the note.

    In all cases except "exception", expr is the Symbolic expression
    that must be equal to val to follow this schedule step.
    """

    def __init__(self, typ, expr, val):
        if typ not in ("branch_nondet", "branch_det", "exception",
                       "assumption", "note"):
            raise ValueError("Bad SchedNode type %r" % typ)
        self.typ = typ
        self.expr = expr
        self.val = val

        # Unwind out of this module and record the call stack
        frames = [inspect.getframeinfo(frrec[0], 3)
                  for frrec in inspect.stack()]
        for i, frame in enumerate(frames):
            if frames[0].filename != frame.filename:
                break
        self.frames = frames[i:]

    def __repr__(self):
        return "SchedNode(%r, %r, %r)" % (self.typ, self.expr, self.val)

    def is_branch(self):
        return self.typ == "branch_nondet" or self.typ == "branch_det"

    def path_expr(self):
        """Return the path condition expression for this node."""
        if self.val == True:
            return self.expr
        elif self.val == False:
            return symnot(self.expr)
        raise ValueError("No path expression for %r" % self)

class Scheduler(object):
    """Tracks the schedule for the current symbolic apply."""

    def __init__(self):
        # Stack of schedules; each schedule is a list of SchedNodes
        self.schedq = []

        # Prime the schedule
        self.queue_schedule([])

    def queue_schedule(self, s):
        self.schedq.append(s)

    def schedule_generator(self):
        while len(self.schedq) > 0:
            yield self.schedq.pop()

class PathState(object):
    """Tracks state for the current symbolic execution code path."""

    def __init__(self, sched):
        self.sched = sched
        self.schedidx = 0
        self.solver = z3.Solver()

    def str_path(self):
        """Return the current path constraint as a string."""

        out = []
        for node in self.sched[:self.schedidx]:
            if node.typ in ("exception", "note"):
                note = str(node.val)
            else:
                note = str(simplify(node.path_expr()))
                #note = str(node.path_expr())
            if "\n" in note:
                note = "\n  " + note.replace("\n", "\n  ")
            out.append("%s:%s: %s" %
                       (os.path.basename(node.frames[0].filename),
                        node.frames[0].lineno, note))
        return "\n".join(out)

def note(note):
    """Record a user-defined note in the current schedule."""

    path_state = Env.path_state()
    cursched = path_state.sched
    if len(cursched) == path_state.schedidx:
        cursched.append(SchedNode("note", None, note))
    else:
        # Check for replay divergence
        node = cursched[path_state.schedidx]
        if node.typ != "note":
            raise ReplayDivergedError(node, "note")
    path_state.schedidx += 1

def simplify(expr, try_harder=False):
    expr = unwrap(expr)
    if not z3.is_ast(expr):
        return expr
    core_simplifier = 'ctx-simplify'
    if try_harder:
        ## ctx-solver-simplify is very slow; use the
        ## faster but less powerful ctx-simplify.
        core_simplifier = 'ctx-solver-simplify'
    t = z3.Repeat(z3.Then(z3.With('simplify', expand_select_store=True,
                                              ite_extra_rules=True,
                                              expand_store_eq=True),
                          'propagate-values',
                          'ctx-simplify',
                          core_simplifier,
                          ))
    subgoals = t(expr)
    if len(subgoals[0]) == 0:
        s = wrap(z3.BoolVal(True))
    else:
        s = wrap(z3.simplify(unwrap(symand([symand(wraplist(g))
                                            for g in subgoals]))))
    return s

def assume(e):
    """Declare symbolic expression e to be True."""

    if e is True:
        return

    scheduler, path_state = Env.scheduler(), Env.path_state()

    # Is this assumption already implied?  This isn't strictly
    # necessary, but it cleans up generated expressions and the
    # execution graph.  It also sometimes lets z3 decide a path
    # condition that it otherwise can't (which is probably a z3 bug).
    solver = path_state.solver
    solver.push()
    solver.add(unwrap(symnot(e)))
    sat = solver.check()
    solver.pop()
    if sat == z3.unsat:
        return

    # Update the schedule and execution graph.  (We wouldn't need to
    # track assumptions in the schedule except that we want to avoid
    # duplicate nodes in the execution graph.)
    cursched = path_state.sched
    if len(cursched) == path_state.schedidx:
        cursched.append(SchedNode("assumption", e, True))
    else:
        # Check for replay divergence
        node = cursched[path_state.schedidx]
        if node.typ != "assumption":
            raise ReplayDivergedError(node, "assumption")
        if not node.expr.eq(e):
            raise ReplayDivergedError(node.expr, e)
    path_state.schedidx += 1

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

class SymbolicApplyResult(object):
    """The result of a symbolic application.

    This can be a returned value or an exception."""

    def __init__(self, typ, value, env):
        self.__typ = typ
        self.__value = value
        self.__var_constructors = env.var_constructors
        self.__const_types = env.const_types
        self.__schedule = env.path_state.sched
        self.__internal_vals = None

        # XXX Should this include deterministic branches?  We have in
        # the past, but there's probably no reason to
        self.__path_condition_list \
            = self.get_path_condition_list(with_assume=True, with_det=True)

    @property
    def type(self):
        """The type of this result, as a string.

        This is either "value" or "exception".
        """
        return self.__typ

    @property
    def value(self):
        """The value returned by the application (which may be Symbolic).

        Accessing this property throws an exception for non-value
        results.
        """
        if self.__typ != "value":
            raise ValueError("Cannot retrieve value of %s-type result" %
                             self.__typ)
        return self.__value

    @property
    def exc_info(self):
        """The exc_info for the exception thrown by this application.

        Accessing this property throws an exception for non-exception
        results.
        """
        if self.__typ != "exception":
            raise ValueError("Cannot retrieve exception of %s-type result" %
                             self.__typ)
        return self.__value

    def get_path_condition_list(self, with_assume, with_det):
        res = []
        for node in self.__schedule:
            if node.typ == "assumption":
                if with_assume:
                    res.append(node.path_expr())
            elif node.typ == "branch_det":
                if with_det:
                    res.append(node.path_expr())
            elif node.typ == "branch_nondet":
                res.append(node.path_expr())
            elif node.typ == "exception" or node.typ == "note":
                pass
            else:
                raise ValueError("Unexpected SchedNode type %r" % node)
        return res

    @property
    def path_condition_list(self):
        """The path condition of this result, as a list of SBools."""
        return self.__path_condition_list

    @property
    def path_condition(self):
        """The path condition as a single SBool conjunction."""
        return symand(self.__path_condition_list)

    @property
    def pathid(self):
        """Return a string that uniquely identifies this path.

        The returned string will consist of a 'p' followed by hex
        digits.  This is formed by creating a bit string from left to
        right representing each fork in the path, padding its length
        to a multiple of 4, and converting this to hex.  As a result,
        strings with identical prefixes represent code paths with
        identical prefixes.
        """
        bitstring = length = 0
        for node in self.__schedule:
            if node.typ == "branch_nondet":
                bitstring = (bitstring << 1) | node.val
                length += 1
            elif node.typ in ("branch_det", "assumption", "note"):
                continue
            elif node.typ == "exception" and node is self.__schedule[-1]:
                bitstring = (bitstring << 1) | node.expr
                length += 1
            else:
                raise ValueError("Can't encode schedule node %r" % node)
        # Pad the bitstring to a multiple of four
        bitstring <<= 3 - ((length + 3) % 4)
        # Convert to hex
        return "p%0*.x" % ((length + 3) / 4, bitstring)

    @property
    def internals(self):
        """The list of internal Symbolic values created by this path.

        These are any values whose names begin with "internal_".
        """
        if self.__internal_vals is None:
            # Map internal variable names to values
            self.__internal_vals = []
            for name, ctor in self.__var_constructors.iteritems():
                if name.startswith('internal_'):
                    self.__internal_vals.append(ctor(name, MODEL_FETCH))
        return self.__internal_vals

    def get_model(self, z3_model=None):
        """Return a Model interpreting the variables declared by this code path.

        The returned Model represents satisfying, concrete assignments
        consistent with self's path condition for all of the variables
        created by self's code path.

        By default, this will construct a model from the path
        condition, but the caller can also provide a specific Z3 model
        (which must be consistent with the path condition).
        """

        if z3_model is None:
            z3_model = check(self.path_condition).z3_model

        return Model(self.__var_constructors, z3_model)

    def symbolic_type(self, const):
        """Return a representation of the Symbolic type of a Z3 constant.

        const must satisfy z3.is_const.  This will map its type back
        to a pseudo-Symbolic type.  Because the Z3 type hierarchy does
        not match the Symbolic type hierarchy, const may not have a
        direct mapping to a Symbolic type, so this pseudo-Symbolic
        type will have one of the following forms:

        * Symbolic subclass - An exact Symbolic type.  This will be a
          synonym type if possible (this allows additional information
          to be associated with the Symbolic type that would otherwise
          be lost inside Z3).

        * (index pseudo-Symbolic type, value pseudo-Symbolic type) - A
          Z3 array from the index to the value type.
        """

        # XXX The result of this will only give Symbolic types for
        # primitives.  Should this perhaps represent the whole type
        # hierarchy?  Like
        #  ("struct", SStruct | SSynonym, field type) |
        #  ("map", SMap | SSynonym, index type, value type) |
        #  ("primitive", type)

        outer_type, path = self.__const_types[str(const)]
        def rec(outer_type, path):
            if issubclass(outer_type, SStructBase) and len(path):
                return rec(outer_type._fields[path[0]], path[1:])
            elif issubclass(outer_type, SMapBase):
                return (rec(outer_type._indexType, ()),
                        rec(outer_type._valueType, path))
            elif issubclass(outer_type, SymbolicConst) and not len(path):
                return outer_type
            else:
                raise Exception("Failed to resolve type of %s" % const)
        return rec(outer_type, path)

def symbolic_apply(fn, *args):
    """Evaluate fn(*args) under symbolic execution.

    This yields a series of SymbolicApplyResult objects; one for each
    distinct code path.  If a code path leads to an uncheckable
    constraint, this returns an exception-type result.
    """

    if Env.current() != Env.global_env:
        raise Exception("Recursive symbolic_apply")

    # Since this is an iterator, the caller might change things in the
    # global environment between code paths.  We want to start each
    # code path from the same environment, so snapshot it now.
    root_env = Env(Env.current())
    scheduler = Scheduler()
    graph = SchedGraph()

    for cursched in scheduler.schedule_generator():
        old_env = Env.current()
        path_state = PathState(cursched)
        Env(root_env, scheduler, path_state).activate()
        sar = None
        try:
            rv = fn(*args)
            sar = SymbolicApplyResult("value", rv, Env.current())
            graph.add_sched(path_state.sched, str(rv))
        except UnsatisfiablePath:
            graph.add_sched(path_state.sched, "Unsatisfiable path", "blue")
            raise
        except UncheckableConstraintError as e:
            import traceback
            traceback.print_exc()
            print >>sys.stderr, "Ignoring path with uncheckable constraint"
            sar = SymbolicApplyResult("exception", sys.exc_info(), Env.current())
            graph.add_sched(path_state.sched, "Exception: " + str(e), "red")
        except Exception as e:
            graph.add_sched(path_state.sched, "Exception: " + str(e), "red")
            if len(e.args) == 1:
                e.args = ('%s in symbolic state:\n%s' %
                          (e.args[0], path_state.str_path()),)
            else:
                e.args = e.args + (path_state.str_path(),)
            graph.show()
            raise
        finally:
            old_env.activate()

        if sar is not None:
            yield sar

#    graph.show()

class CheckResult(object):
    def __init__(self, z3_result, extra=None):
        self.z3_result = z3_result
        self.result = str(z3_result)
        self.is_sat = (z3_result == z3.sat)
        self.is_unsat = (z3_result == z3.unsat)
        self.is_unknown = (z3_result == z3.unknown)
        self.__extra = extra

    @property
    def z3_model(self):
        if self.is_sat:
            return self.__extra
        raise ValueError("%s result has no model" % self.result)

    @property
    def reason(self):
        if self.is_unknown:
            return self.__extra
        raise ValueError("%s result has no unknown reason" % self.result)

def check(e):
    solver = z3.Solver()
    solver.add(unwrap(e))
    c = solver.check()
    if c == z3.sat:
        return CheckResult(c, solver.model())
    elif c == z3.unknown:
        return CheckResult(c, solver.reason_unknown())
    return CheckResult(c)

class Model(object):
    """A Model interprets symbolic expressions into concrete values.

    A Model object is indexed using the variable names that were
    provided by the user for calls to Symbolic.var and constVal and
    their ilk.  Indexing into the Model will return concrete Python
    values or compound values that support indexing and field
    selection just like during symbolic execution.
    """

    # The main complication here is that the Z3 constant names are
    # derived from user-provided names, but may not be identical in
    # the presence of compound types.  Hence, we actually use the same
    # Symbolic types as the original variables were declared as to get
    # the exact same expression transformations that we got during
    # symbolic execution.  The difference is that we pass the model in
    # to this instance hierarchy and when we reach a base value, we
    # evaluate the expression used to reach the value in the model to
    # get a concrete value.

    def __init__(self, var_constructors, z3_model):
        self.__var_constructors = var_constructors
        self.__z3_model = z3_model
        self.__track = False
        self.__asignments = collections.defaultdict(list)

    def __getitem__(self, name):
        # XXX This is good for things where the initial variable name
        # is known, but it's no good for evaluating symbolic values
        # returned from symbolic execution (it's also a bit confusing
        # for mutable variables, since it evaluates their initial
        # value, not their final value).  _eval is only suited to leaf
        # values.  Maybe 'bind'?
        #
        # The other problem with this is that sometimes I *want* the
        # symbolic expression (e.g., in fs_testgen's "other pipe FDs"
        # test), but this is a one-way street.  Maybe I should bind
        # symbolic values to a model, but ultimately forcing them to a
        # concrete value should be done not when I happen to reach a
        # leaf in the type, but should require some extra step, like
        # accessing a "val" property.
        return self.__var_constructors[name](name, self)

    def track_assignments(self, enable=True):
        """Enable or disable assignment tracking."""
        self.__track = enable

    def assignments(self):
        """Return the expressions evaluated by the model.

        The returned value is a dictionary mapping from assignment
        realms to lists, where each list consists of pairs of
        (expression, value).  Both expression and value are instances
        of Symbolic.  The list will be in the order the expressions
        were evaluated, with duplicate expressions suppressed.
        """
        return self.__asignments

    def _eval(self, expr, realm=None):
        """Evaluate a Symbolic expression to a concrete Python value."""

        # model_completion asks Z3 to make up concrete values if they
        # are not interpreted in the model.
        z3val = self.__z3_model.evaluate(unwrap(expr), model_completion=True)
        res = to_concrete(z3val, type(expr))

        if self.__track and realm is not REALM_IGNORE:
            for aexpr, _ in self.__asignments[realm]:
                if unwrap(expr).eq(unwrap(aexpr)):
                    break
            else:
                val = type(expr)._wrap(z3val, None)
                self.__asignments[realm].append((expr, val))

        return res

#
# Utilities
#

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__

def to_concrete(expr, expr_type=None):
    if z3.is_ast(expr):
        if expr_type is None:
            raise TypeError("to_concrete cannot be applied to a Z3 value")
    elif not isinstance(expr, Symbolic):
        return expr
    z3val = unwrap(expr)
    if z3.is_int_value(z3val):
        return z3val.as_long()
    if z3.is_true(z3val):
        return True
    if z3.is_false(z3val):
        return False
    if z3val.sort_kind() == z3.Z3_UNINTERPRETED_SORT:
        if expr_type is None:
            expr_type = type(expr)
        return expr_type._wrap(z3val, None)
    # Either expr is not a concrete value, or we don't know how to
    # extract its concrete value (it could be, e.g., an enum value)
    # XXX Use sexpr because regular formatting has been freezing on
    # me.
    raise Exception("Expression %s => %s is not a concrete value" %
                    (expr, z3val.sexpr()))
