import sys
import os
import z3
import types

class Symbolic(object):
    pass

def toz3(val):
    if isinstance(val, Symbolic):
        return val._v
    return val

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__

solver = z3.Solver()

def str_state():
    asserts = solver.assertions()
    return str(z3.simplify(z3.And(*asserts)))

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

class SList(object):
    def __init__(self, name, valSort):
        self._vals = z3.Array(name, z3.IntSort(), valSort)
        self._len = make_sexpr(z3.Int(name + '.len'))
        assume(self._len >= 0)

    def __check_idx(self, idx):
        if idx < 0:
            raise IndexError("SList index out of range: %r < %r" % (idx, 0))
        if idx >= self.len():
            raise IndexError("SList index out of range: %r >= %r" %
                             (idx, self._len))
        return toz3(idx)

    def __getitem__(self, idx):
        return make_sexpr(self._vals[self.__check_idx(idx)])

    def __setitem__(self, idx, val):
        self._vals = z3.Store(self._vals, self.__check_idx(idx), toz3(val))

    def __eq__(self, o):
        if not isinstance(o, SList):
            return NotImplemented
        return make_sexpr(z3.And(toz3(self._len) == toz3(o._len),
                                 self._vals == o._vals))

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return make_sexpr(z3.Not(toz3(r)))

    def len(self):
        # Overriding __len__ isn't useful because the len() builtin
        # will try hard to coerce it to an integer.
        return self._len

    def append(self, val):
        l = self.len()
        self._len += 1
        self[l] = val

class SDict(object):
    def __init__(self, name, keySort, valSort):
        self._map = z3.Array(name, keySort, valSort)
        self._valid = z3.Array(name + '.valid', keySort, z3.BoolSort())

    def __getitem__(self, key):
        key = toz3(key)
        if self._valid[key]:
            return self._map[key]
        raise KeyError(key)

    def __setitem__(self, key, val):
        key, val = toz3(key), toz3(val)
        self._valid = z3.Store(self._valid, key, True)
        self._map = z3.Store(self._map, key, val)

    def __eq__(self, o):
        if not isinstance(o, SDict):
            return NotImplemented
        return make_sexpr(z3.And(toz3(self._valid == o._valid),
                                 toz3(self._map == o._map)))

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return make_sexpr(z3.Not(toz3(r)))

class SBag(object):
    def __init__(self, name):
        self._name_prefix = name
        self._items = []
        self._choices = 0

    def add(self, v):
        self._items.append(v)

    def choose(self):
        self._choices = self._choices + 1
        choicevar = anyInt('%s.choose.%d' % (self._name_prefix, self._choices))
        for i in range(0, len(self._items)):
            if choicevar == i:
                return self._items[i]

        ## the bag also contains arbitrary other items
        newvar = anyInt('%s.someitem.%d' % (self._name_prefix, self._choices))
        return newvar

    def __eq__(self, o):
        if not isinstance(o, SBag):
            return False

        ol = list(o._items)
        for e1 in self._items:
            found = False
            for e2 in ol:
                if e1 == e2:
                    ol.remove(e2)
                    found = True
                    break
            if not found:
                return False
        return True

    def __ne__(self, o):
        return not self.__eq__(o)

def make_sexpr(ref):
    ## handle concrete types
    if isinstance(ref, bool):
        return ref

    if isinstance(ref, z3.ArithRef):
        return SArith(ref)
    if isinstance(ref, z3.BoolRef):
        return SBool(ref)
    return SExpr(ref)

def anyInt(name):
    return make_sexpr(z3.Int(name))

def anyListOfInt(name):
    return SList(name, z3.IntSort())

def anyDictOfIntToInt(name):
    return SDict(name, z3.IntSort(), z3.IntSort())

def assume(e):
    solver.add(toz3(e))
    sat = solver.check()
    if sat == z3.unsat:
        raise RuntimeError("Unsatisfiable assumption")
    elif sat != z3.sat:
        raise RuntimeError("Uncheckable assumption")

def symbolic_apply(fn, *args):
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
            print >>sys.stderr, "  If %s" % \
                str_state().replace("\n", "\n" + " "*5)
            lines = traceback.format_exception_only(etype, value)
            for line in lines:
                sys.stderr.write(line)
        sys.exit(0)
    os.waitpid(child, 0)



class Struct(object):
    def __eq__(self, o):
        if self.__class__ != o.__class__:
            return NotImplemented
        for field in self.__slots__:
            if getattr(self, field) != getattr(o, field):
                return False
        return True

    def __ne__(self, o):
        r = (self == o)
        if r is NotImplemented:
            return NotImplemented
        return not r

class State(Struct):
    __slots__ = ["counter"]

    def __init__(self):
        # XXX This name matters since it connects the initial counter
        # value of different State objects.  Will this scale to more
        # complex state?
        self.counter = anyInt('State.counter')
        assume(self.counter >= 0)

    def sys_inc(self):
        self.counter = self.counter + 1

    def sys_dec(self):
        self.counter = self.counter - 1

    def sys_iszero(self):
        return self.counter == 0

class Pipe(Struct):
    __slots__ = ['elems', 'nread']

    def __init__(self):
        self.elems = anyListOfInt('Pipe.elems')
        self.nread = anyInt('Pipe.nread')

        assume(self.nread >= 0)
        assume(self.nread <= self.elems.len())

    def write(self, elem):
        self.elems.append(elem)

    def read(self):
        if self.elems.len() == self.nread:
            return None
        else:
            e = self.elems[self.nread]
            self.nread = self.nread + 1
            return e

    def write_a(self):
        self.write(anyInt('Pipe.writeitem.a'))

    def write_b(self):
        self.write(anyInt('Pipe.writeitem.b'))

class UnordPipe(Struct):
    __slots__ = ['elems', 'nitem']

    def __init__(self):
        self.elems = SBag('UnordPipe.items')
        self.nitem = anyInt('UnordPipe.nitem')

        assume(self.nitem >= 0)

    def u_write(self, elem):
        self.elems.add(elem)
        self.nitem = self.nitem + 1

    def u_read(self):
        if self.nitem == 0:
            return None
        else:
            e = self.elems.choose()
            self.nitem = self.nitem - 1
            return e

    def u_write_a(self):
        self.u_write(anyInt('UnordPipe.writeitem.a'))

    def u_write_b(self):
        self.u_write(anyInt('UnordPipe.writeitem.b'))

def test(base, call1, call2):
    print "%s %s" % (call1.__name__, call2.__name__)

    s1 = base()
    r11 = call1(s1)
    r12 = call2(s1)

    s2 = base()
    r21 = call2(s2)
    r22 = call1(s2)

    if r11 != r22 or r12 != r21:
        res = "results diverge"
    elif s1 != s2:
        res = "state diverges"
    else:
        res = "commute"

    asserts = solver.assertions()
    if len(asserts) == 0:
        # XXX What if we have assertions, but they're vacuously true?
        print "  any state:", res
    else:
        print "  %s: %s" % \
            (str_state().replace("\n", "\n  "), res)

tests = [
    (State, [State.sys_inc, State.sys_dec, State.sys_iszero]),
    (Pipe, [Pipe.write_a, Pipe.write_b, Pipe.read]),
    (UnordPipe, [UnordPipe.u_write_a, UnordPipe.u_write_b, UnordPipe.u_read]),
]

for (base, calls) in tests:
    for i in range(len(calls)):
        for j in range(i, len(calls)):
            symbolic_apply(test, base, calls[i], calls[j])
    print
