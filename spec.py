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
        fieldeqs = [getattr(self, field) == getattr(o, field)
                    for field in self.__slots__]
        return simsym.symand(fieldeqs)

    def __ne__(self, o):
        r = (self == o)
        if r is NotImplemented:
            return NotImplemented
        return simsym.symnot(r)

class State(Struct):
    __slots__ = ["counter"]

    def __init__(self):
        # XXX This name matters since it connects the initial counter
        # value of different State objects.  Will this scale to more
        # complex state?
        self.counter = simsym.SInt.any('State.counter')
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
        self.nread = simsym.SInt.any('Pipe.nread')

        simsym.assume(self.nread >= 0)
        simsym.assume(self.nread <= self.elems.len())

    def write(self, which):
        elem = simsym.SInt.any('Pipe.write[%s].data' % which)
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
        self.nitem = simsym.SInt.any('UPipe.nitem')

        simsym.assume(self.nitem >= 0)

    def u_write(self, which):
        elem = simsym.SInt.any('UPipe.write[%s].data' % which)
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
        self.numifree = simsym.SInt.any('Fs.numifree')

        simsym.assume(self.numifree >= 0)
        fn = simsym.unwrap(simsym.SInt.any('fn'))
        simsym.assume(z3.ForAll(fn,
                         z3.Implies(self.fn_to_ino._valid[fn],
                                    self.ino_to_data._valid[self.fn_to_ino._map[fn]])))

    def iused(self, ino):
        fn = simsym.unwrap(simsym.SInt.any('fn'))
        return simsym.wrap(z3.Exists(fn,
                              z3.And(self.fn_to_ino._valid[fn],
                                     self.fn_to_ino._map[fn] == simsym.unwrap(ino))))

    def idecref(self, ino):
        if not self.iused(ino):
            self.numifree = self.numifree + 1

    def open(self, which):
        fn = simsym.SInt.any('Fs.open[%s].fn' % which)
        creat = simsym.SBool.any('Fs.open[%s].creat' % which)
        excl = simsym.SBool.any('Fs.open[%s].excl' % which)
        trunc = simsym.SBool.any('Fs.open[%s].trunc' % which)
        if creat:
            if not self.fn_to_ino.contains(fn):
                if self.numifree == 0:
                    return ('err', errno.ENOSPC)
                ino = simsym.SInt.any('Fs.open[%s].ialloc' % which)
                simsym.add_internal(ino)
                simsym.assume(simsym.symnot(self.iused(ino)))
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
        src = simsym.SInt.any('Fs.rename[%s].src' % which)
        dst = simsym.SInt.any('Fs.rename[%s].dst' % which)
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
        fn = simsym.SInt.any('Fs.unlink[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        del self.fn_to_ino[fn]
        self.idecref(ino)
        return ('ok',)

    def link(self, which):
        oldfn = simsym.SInt.any('Fs.link[%s].oldfn' % which)
        newfn = simsym.SInt.any('Fs.link[%s].newfn' % which)
        if not self.fn_to_ino.contains(oldfn):
            return ('err', errno.ENOENT)
        if self.fn_to_ino.contains(newfn):
            return ('err', errno.EEXIST)
        self.fn_to_ino[newfn] = self.fn_to_ino[oldfn]
        return ('ok',)

    def read(self, which):
        fn = simsym.SInt.any('Fs.read[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        return ('data', self.ino_to_data[ino])

    def write(self, which):
        fn = simsym.SInt.any('Fs.write[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        data = simsym.SInt.any('Fs.write[%s].data' % which)
        self.ino_to_data[ino] = data
        return ('ok',)

def test(base, *calls):
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

        diverge = ''
        if simsym.symor([all_r[0] != r for r in all_r[1:]]):
            diverge = diverge + 'r'
        if simsym.symor([all_s[0] != s for s in all_s[1:]]):
            diverge = diverge + 's'
        return diverge
    except PreconditionFailure:
        return None

tests = [
    (State, 3, {},
     [State.sys_inc, State.sys_dec, State.sys_iszero]),
    (Pipe,  3, {},
     [Pipe.write, Pipe.read]),
    (UPipe, 3, {},
     [UPipe.u_write, UPipe.u_read]),
    (Fs,    2, {'first': lambda(x): x[0]},
     [Fs.open, Fs.read, Fs.write, Fs.unlink, Fs.link, Fs.rename]),
]

def projected_call(pname, pf, method):
    def wrapped(*args, **kwargs):
        return pf(method(*args, **kwargs))
    wrapped.__name__ = '%s:%s' % (method.__name__, pname)
    return wrapped

z3printer._PP.max_lines = float('inf')
for (base, ncomb, projections, calls) in tests:
    projected_calls = list(calls)
    for p in projections:
        for c in calls:
            projected_calls.append(projected_call(p, projections[p], c))
    for callset in itertools.combinations_with_replacement(projected_calls, ncomb):
        print ' '.join([c.__name__ for c in callset])
        rvs = simsym.symbolic_apply(test, base, *callset)
        conds = collections.defaultdict(lambda: simsym.wrap(z3.BoolVal(False)))
        for (cond, res) in simsym.combine(rvs):
            conds[res] = cond

        pc = simsym.simplify(conds[''])
        pr = simsym.simplify(simsym.symor([conds['r'], conds['rs']]))
        ps = simsym.simplify(conds['s'])

        ex_pc = simsym.exists(simsym.internals(), pc)
        nex_pc = simsym.symnot(ex_pc)
        ex_pr = simsym.exists(simsym.internals(), pr)
        nex_pr = simsym.symnot(ex_pr)
        ps2 = simsym.symand([ps, nex_pc, nex_pr])

        ps_ex_pr = simsym.symand([ps, ex_pr])
        pr2 = simsym.symand([simsym.symor([pr, ps_ex_pr]), nex_pc])

        ps_ex_pc = simsym.symand([ps, ex_pc])
        pr_ex_pc = simsym.symand([pr, ex_pc])
        pc2 = simsym.symor([pc, ps_ex_pc, pr_ex_pc])

        for msg, cond in (('commute', pc2),
                          ('results diverge', pr2),
                          ('states diverge', ps2)):
            if simsym.check(cond) == z3.unsat:
                continue
            if simsym.check(simsym.symnot(cond)) == z3.unsat:
                s = 'any state'
            else:
                scond = simsym.simplify(cond)
                s = '\n    ' + str(scond).replace('\n', '\n    ')
            print '  %s: %s' % (msg, s)
    print
