import sys
import os
import z3
import types

class Symbolic(object):
    pass

def toz3(v):
    if isinstance(v, Symbolic):
        return v._v
    return v

def strtype(x):
    if type(x) == types.InstanceType:
        return x.__class__.__name__
    else:
        return type(x).__name__

solver = z3.Solver()

class SExpr(Symbolic):
    def __init__(self, ref):
        if not isinstance(ref, z3.ExprRef):
            raise TypeError("SExpr expected ExprRef, got %s" % strtype(ref))
        self._v = ref

    def __eq__(self, o):
        return make_sexpr(self._v == toz3(o))

    def __ne__(self, o):
        return make_sexpr(self._v != toz3(o))

class SArith(SExpr):
    def __init__(self, ref):
        if not isinstance(ref, z3.ArithRef):
            raise TypeError("SArith expected ArithRef, got %s" % strtype(ref))
        super(SArith, self).__init__(ref)

    def __add__(self, o):
        return make_sexpr(self._v + toz3(o))

    def __sub__(self, o):
        return make_sexpr(self._v - toz3(o))

    def __nonzero__(self):
        return bool(self == 0)

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

def symbolic_apply(fn, *args):
    # XXX We could avoid this fork if we were smarter about cleaning
    # up all but the first code path
    # XXX Return a list of return values of fn.
    child = os.fork()
    if child == 0:
        # XXX Exceptions?
        fn(*args)
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

    def sys_inc(self):
        self.counter = self.counter + 1

    def sys_dec(self):
        self.counter = self.counter - 1

    def sys_iszero(self):
        return self.counter == 0

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

    solver.check()
    model = solver.model()
    if len(model) == 0:
        print "  any state:", res
    else:
        print "  %s:" % model, res

calls = [State.sys_inc, State.sys_dec, State.sys_iszero]
for i in range(len(calls)):
    for j in range(i, len(calls)):
        symbolic_apply(test, State, calls[i], calls[j])
