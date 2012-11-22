import simsym
import symtypes
import z3
import errno
import sys

class PreconditionFailure(Exception):
    def __init__(self): pass

class Struct(object):
    __slots__ = []

    def __eq__(self, o):
        if self.__class__ != o.__class__:
            return NotImplemented
        # XXX Should this indicate what field is not equal?
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
        self.counter = simsym.anyInt('State.counter')
        simsym.assume(self.counter >= 0)

    def sys_inc(self, which):
        self.counter = self.counter + 1

    def sys_dec(self, which):
        if self.counter == 0:
            raise PreconditionFailure()
        self.counter = self.counter - 1

    def sys_iszero(self, which):
        return self.counter == 0

class Pipe(Struct):
    __slots__ = ['elems', 'nread']

    def __init__(self):
        self.elems = symtypes.anyListOfInt('Pipe.elems')
        self.nread = simsym.anyInt('Pipe.nread')

        simsym.assume(self.nread >= 0)
        simsym.assume(self.nread <= self.elems.len())

    def write(self, which):
        elem = simsym.anyInt('Pipe.write.%s' % which)
        self.elems.append(elem)

    def read(self, which):
        if self.elems.len() == self.nread:
            return None
        else:
            e = self.elems[self.nread]
            self.nread = self.nread + 1
            return e

class UnordPipe(Struct):
    __slots__ = ['elems', 'nitem']

    def __init__(self):
        self.elems = symtypes.SBag('UnordPipe.items')
        self.nitem = simsym.anyInt('UnordPipe.nitem')

        simsym.assume(self.nitem >= 0)

    def u_write(self, which):
        elem = simsym.anyInt('UnordPipe.write.%s' % which)
        self.elems.add(elem)
        self.nitem = self.nitem + 1

    def u_read(self, which):
        if self.nitem == 0:
            return None
        else:
            e = self.elems.choose()
            self.nitem = self.nitem - 1
            return e

class Fs(Struct):
    __slots__ = ['fn_to_ino', 'ino_to_data', 'ialloc', 'numialloc']

    def __init__(self):
        self.fn_to_ino = symtypes.anyDictOfIntToInt('Fs.dir')
        self.ino_to_data = symtypes.anyDictOfIntToInt('Fs.idata')
        self.ialloc = symtypes.anyListOfBool('Fs.ialloc')
        self.numialloc = simsym.anyInt('Fs.numialloc')

        # XXX how to represent inode refcount constraints?

        simsym.assume(self.numialloc <= self.ialloc._len)
        fn = simsym.unwrap(simsym.anyInt('fn'))
        ino = simsym.unwrap(simsym.anyInt('ino'))
        simsym.assume(z3.ForAll(fn,
                         z3.Implies(self.fn_to_ino._valid[fn],
                                    self.ino_to_data._valid[self.fn_to_ino._map[fn]])))
        simsym.assume(z3.ForAll(fn,
                         z3.Implies(self.fn_to_ino._valid[fn],
                            z3.And(self.fn_to_ino._map[fn] < simsym.unwrap(self.ialloc._len),
                                   self.fn_to_ino._map[fn] >= 0,
                                   self.ialloc._vals[self.fn_to_ino._map[fn]]))))

        ## XXX the solver times out with this assumption.
        if False:
            simsym.assume(z3.ForAll(ino,
                             z3.Implies(self.ialloc._vals[ino],
                                        z3.Exists(fn,
                                                  z3.And(self.fn_to_ino._valid[fn],
                                                         self.fn_to_ino._map[fn] == ino)))))

    def open(self, which):
        fn = simsym.anyInt('Fs.open.fn.%s' % which)
        creat = simsym.anyBool('Fs.open.creat.%s' % which)
        excl = simsym.anyBool('Fs.open.excl.%s' % which)
        trunc = simsym.anyBool('Fs.open.trunc.%s' % which)
        if creat:
            if not self.fn_to_ino.contains(fn):
                # XXX need a better plan for allocating a free inode!
                if self.numialloc == self.ialloc._len:
                    return ('err', errno.ENOSPC)
                self.numialloc = self.numialloc + 1
                ino = simsym.anyInt('Fs.open.ialloc.%s' % which)
                if ino < 0 or ino >= self.ialloc._len or self.ialloc[ino]:
                    sys.exit(0)   ## XXX cleaner API?
                self.ialloc[ino] = True
                self.ino_to_data[ino] = 0
                self.fn_to_ino[fn] = ino
            else:
                if excl: return ('err', errno.EEXIST)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        if trunc:
            self.ino_to_data[self.fn_to_ino[fn]] = 0
        return ('ok',)

    def unlink(self, which):
        fn = simsym.anyInt('Fs.unlink.fn.%s' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        del self.fn_to_ino[fn]
        self.numialloc = self.numialloc - 1
        self.ialloc[ino] = False
        # XXX inode refcount?
        return ('ok')

    def read(self, which):
        fn = simsym.anyInt('Fs.read.fn.%s' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        return ('data', self.ino_to_data[ino])

    def write(self, which):
        fn = simsym.anyInt('Fs.write.fn.%s' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        data = simsym.anyInt('Fs.write.data.%s' % which)
        self.ino_to_data[ino] = data
        return ('ok',)

def test(base, call1, call2):
    print "%s %s" % (call1.__name__, call2.__name__)

    try:
        s1 = base()
        r11 = call1(s1, 'a')
        r12 = call2(s1, 'b')

        s2 = base()
        r21 = call2(s2, 'b')
        r22 = call1(s2, 'a')

        if r11 != r22 or r12 != r21:
            res = "results diverge"
        elif s1 != s2:
            res = "state diverges"
        else:
            res = "commute"

        state = simsym.str_state()
        if state is None:
            # XXX What if we have assertions, but they're vacuously true?
            # XXX Can we filter out explicit assumptions?  I think we're
            # only interested in the path condition.
            print "  any state:", res
        else:
            print "  %s: %s" % \
                (state.replace("\n", "\n  "), res)
    except PreconditionFailure:
        pass

tests = [
    (State, [State.sys_inc, State.sys_dec, State.sys_iszero]),
    (Pipe, [Pipe.write, Pipe.read]),
    (UnordPipe, [UnordPipe.u_write, UnordPipe.u_read]),
    (Fs, [Fs.open, Fs.read, Fs.write, Fs.unlink]),
]

for (base, calls) in tests:
    for i in range(len(calls)):
        for j in range(i, len(calls)):
            simsym.symbolic_apply(test, base, calls[i], calls[j])
    print
