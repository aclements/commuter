import simsym
import symtypes
import z3
import errno

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
        elem = simsym.anyInt('Pipe.write[%s].data' % which)
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
        elem = simsym.anyInt('UnordPipe.write[%s].data' % which)
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
    __slots__ = ['fn_to_ino', 'ino_to_data', 'numifree']

    def __init__(self):
        self.fn_to_ino = symtypes.anyDictOfIntToInt('Fs.dir')
        self.ino_to_data = symtypes.anyDictOfIntToInt('Fs.idata')
        self.numifree = simsym.anyInt('Fs.numifree')

        simsym.assume(self.numifree >= 0)
        fn = simsym.unwrap(simsym.anyInt('fn'))
        simsym.assume(z3.ForAll(fn,
                         z3.Implies(self.fn_to_ino._valid[fn],
                                    self.ino_to_data._valid[self.fn_to_ino._map[fn]])))

    def iused(self, ino):
        fn = simsym.unwrap(simsym.anyInt('fn'))
        return simsym.wrap(z3.Exists(fn,
                              z3.And(self.fn_to_ino._valid[fn],
                                     self.fn_to_ino._map[fn] == simsym.unwrap(ino))))

    def idecref(self, ino):
        if not self.iused(ino):
            self.numifree = self.numifree + 1

    def open(self, which):
        fn = simsym.anyInt('Fs.open[%s].fn' % which)
        creat = simsym.anyBool('Fs.open[%s].creat' % which)
        excl = simsym.anyBool('Fs.open[%s].excl' % which)
        trunc = simsym.anyBool('Fs.open[%s].trunc' % which)
        if creat:
            if not self.fn_to_ino.contains(fn):
                if self.numifree == 0:
                    return ('err', errno.ENOSPC)
                ino = simsym.anyInt('Fs.open[%s].ialloc' % which)
                simsym.require(simsym.wrap(z3.Not(simsym.unwrap(self.iused(ino)))))
                self.numifree = self.numifree - 1
                self.ino_to_data[ino] = 0
                self.fn_to_ino[fn] = ino
            else:
                if excl: return ('err', errno.EEXIST)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        if trunc:
            self.ino_to_data[self.fn_to_ino[fn]] = 0
        return ('ok',)

    def rename(self, which):
        src = simsym.anyInt('Fs.rename[%s].src' % which)
        dst = simsym.anyInt('Fs.rename[%s].dst' % which)
        if not self.fn_to_ino.contains(src):
            return ('err', errno.ENOENT)
        if self.fn_to_ino.contains(dst):
            dstino = self.fn_to_ino[dst]
        else:
            dstino = None
        self.fn_to_ino[dst] = self.fn_to_ino[src]
        del self.fn_to_ino[src]
        if dstino is not None:
            self.idecref(dstino)
        return ('ok',)

    def unlink(self, which):
        fn = simsym.anyInt('Fs.unlink[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        del self.fn_to_ino[fn]
        self.idecref(ino)
        return ('ok',)

    def link(self, which):
        oldfn = simsym.anyInt('Fs.link[%s].oldfn' % which)
        newfn = simsym.anyInt('Fs.link[%s].newfn' % which)
        if not self.fn_to_ino.contains(oldfn):
            return ('err', errno.ENOENT)
        if self.fn_to_ino.contains(newfn):
            return ('err', errno.EEXIST)
        self.fn_to_ino[newfn] = self.fn_to_ino[oldfn]
        return ('ok',)

    def read(self, which):
        fn = simsym.anyInt('Fs.read[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        return ('data', self.ino_to_data[ino])

    def write(self, which):
        fn = simsym.anyInt('Fs.write[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        data = simsym.anyInt('Fs.write[%s].data' % which)
        self.ino_to_data[ino] = data
        return ('ok',)

def test(base, call1, call2):
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
    (Fs, [Fs.open, Fs.read, Fs.write, Fs.unlink, Fs.link, Fs.rename]),
]

for (base, calls) in tests:
    for i in range(len(calls)):
        for j in range(i, len(calls)):
            print "%s %s" % (calls[i].__name__, calls[j].__name__)
            simsym.symbolic_apply(test, base, calls[i], calls[j])
    print
