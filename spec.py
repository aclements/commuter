import simsym
import symtypes
import z3
import z3printer
import errno
import collections
import itertools

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

class UPipe(Struct):
    __slots__ = ['elems', 'nitem']

    def __init__(self):
        self.elems = symtypes.SBag('UPipe.items')
        self.nitem = simsym.anyInt('UPipe.nitem')

        simsym.assume(self.nitem >= 0)

    def u_write(self, which):
        elem = simsym.anyInt('UPipe.write[%s].data' % which)
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
                simsym.assume(simsym.wrap(z3.Not(simsym.unwrap(self.iused(ino)))))
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

def test(base, projections, *calls):
    try:
        all_s = []
        all_r = []

        for callseq in itertools.permutations(range(0, len(calls))):
            s = base()
            r = {}
            for idx in callseq:
                r[idx] = calls[idx](s, chr(idx + ord('a')))
            all_s.append(s)
            all_r.append(r)

        diverge = set()

        for s in all_s:
            if len([s2 for s2 in all_s if s != s2]) > 0:
                diverge.add('states')

        for p in projections:
            pf = projections[p]
            for r in all_r:
                if len([r2 for r2 in all_r if pf(r) != pf(r2)]) > 0:
                    diverge.add('results-%s' % p)

        if len(diverge) == 0:
            return 'commute'
        return '%s diverge' % ', '.join(sorted(diverge))
    except PreconditionFailure:
        return None

tests = [
    (State, 3, {'full': lambda(x): x},
     [State.sys_inc, State.sys_dec, State.sys_iszero]),
    (Pipe,  3, {'full': lambda(x): x},
     [Pipe.write, Pipe.read]),
    (UPipe, 3, {'full': lambda(x): x},
     [UPipe.u_write, UPipe.u_read]),
    (Fs,    2, {'full': lambda(x): x, 'first': lambda(x): x[0]},
     [Fs.open, Fs.read, Fs.write, Fs.unlink, Fs.link, Fs.rename]),
]

print_conds = True
z3printer._PP.max_lines = float('inf')
for (base, ncomb, projections, calls) in tests:
    for callset in itertools.combinations_with_replacement(calls, ncomb):
        print ' '.join([c.__name__ for c in callset])
        rvs = simsym.symbolic_apply(test, base, projections, *callset)
        conds = collections.defaultdict(list)
        for (cond, res) in rvs:
            conds[res].append(cond)
        for res in sorted(conds):
            if res is None:
                continue
            else:
                out = '%d paths' % len(conds[res])
                if print_conds:
                    if [] in conds[res]:
                        s = True
                    else:
                        e = z3.Or(*[z3.And(*c) for c in conds[res]])
                        s = simsym.simplify(e)
                    if str(s) == 'True':  ## XXX hack
                        out = out + ', any state'
                    else:
                        out = out + ',\n    %s' % str(s).replace('\n', '\n    ')
                print '  %s: %s' % (res, out)
    print
