import simsym
import symtypes
import z3
import z3printer
import errno
import collections
import itertools
import sys
import argparse
import json

class PreconditionFailure(Exception):
    def __init__(self): pass

class Struct(object):
    __slots__ = []

    def __eq__(self, o):
        if self.__class__ != o.__class__:
            return NotImplemented
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
    ListOfInt = symtypes.tlist(simsym.SInt)

    def __init__(self):
        self.elems = self.ListOfInt.any('Pipe.elems')
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

class SFn(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Fn')

class SIno(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Ino')

class SData(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Data')

class Fs(Struct):
    __slots__ = ['fn_to_ino', 'ino_to_data', 'numifree']
    FilenameToInode = symtypes.tdict(SFn, SIno)
    InodeToData = symtypes.tdict(SIno, SData)
    data_empty = SData.any('Data.empty')

    def __init__(self):
        self.fn_to_ino = self.FilenameToInode.any('Fs.dir')
        self.ino_to_data = self.InodeToData.any('Fs.idata')
        self.numifree = simsym.SInt.any('Fs.numifree')

        simsym.assume(self.numifree < 3)
        fn = SFn.any('fn')

    def iused(self, ino):
        fn = SFn.any('fn')
        # See __init__ above for why we use _map directly.
        return simsym.exists(
            fn, simsym.symand([self.fn_to_ino.contains(fn),
                               self.fn_to_ino._map[fn] == ino]))

    def idecref(self, ino):
        if not self.iused(ino):
            self.numifree = self.numifree + 1

    def open(self, which):
        fn = SFn.any('Fs.open[%s].fn' % which)
        creat = simsym.SBool.any('Fs.open[%s].creat' % which)
        excl = simsym.SBool.any('Fs.open[%s].excl' % which)
        trunc = simsym.SBool.any('Fs.open[%s].trunc' % which)
        if creat:
            if not self.fn_to_ino.contains(fn):
                if self.numifree == 0:
                    return ('err', errno.ENOSPC)
                simsym.assume(self.numifree > 0)
                ino = SIno.any('Fs.open[%s].ialloc' % which)
                simsym.add_internal(ino)
                simsym.assume(simsym.symnot(self.iused(ino)))
                self.numifree = self.numifree - 1
                self.ino_to_data[ino] = self.data_empty
                self.fn_to_ino[fn] = ino
            else:
                if excl: return ('err', errno.EEXIST)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        if trunc:
            self.ino_to_data[self.fn_to_ino[fn]] = self.data_empty
        return ('ok',)

    def rename(self, which):
        src = SFn.any('Fs.rename[%s].src' % which)
        dst = SFn.any('Fs.rename[%s].dst' % which)
        if src == dst:
            return ('ok',)
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
        fn = SFn.any('Fs.unlink[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        del self.fn_to_ino[fn]
        self.idecref(ino)
        return ('ok',)

    def link(self, which):
        oldfn = SFn.any('Fs.link[%s].oldfn' % which)
        newfn = SFn.any('Fs.link[%s].newfn' % which)
        if not self.fn_to_ino.contains(oldfn):
            return ('err', errno.ENOENT)
        if self.fn_to_ino.contains(newfn):
            return ('err', errno.EEXIST)
        self.fn_to_ino[newfn] = self.fn_to_ino[oldfn]
        return ('ok',)

    def read(self, which):
        fn = SFn.any('Fs.read[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        simsym.assume(self.ino_to_data.contains(ino))
        return ('data', self.ino_to_data[ino])

    def write(self, which):
        fn = SFn.any('Fs.write[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        data = SData.any('Fs.write[%s].data' % which)
        simsym.assume(self.ino_to_data.contains(ino))
        self.ino_to_data[ino] = data
        return ('ok',)

    def stat(self, which):
        fn = SFn.any('Fs.stat[%s].fn' % which)
        if not self.fn_to_ino.contains(fn):
            return ('err', errno.ENOENT)
        ino = self.fn_to_ino[fn]
        len = 0
        simsym.assume(self.ino_to_data.contains(ino))
        if self.ino_to_data[ino] != self.data_empty: len = 1

        ## XXX How to compute nlink?

        return ('ok', ino, len)

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

        diverge = ()
        if simsym.symor([all_r[0] != r for r in all_r[1:]]):
            diverge += ('results',)
        if simsym.symor([all_s[0] != s for s in all_s[1:]]):
            diverge += ('state',)
        return diverge
    except PreconditionFailure:
        return None

def projected_call(pname, pf, method):
    def wrapped(*args, **kwargs):
        return pf(method(*args, **kwargs))
    wrapped.__name__ = '%s:%s' % (method.__name__, pname)
    return wrapped

def fnmap(x, fnlist):
    for f in fnlist:
        match = False
        fl = f.as_list()
        for fk, fv in fl[:-1]:
            if fk.eq(x):
                x = fv
                match = True
        if not match:
            x = fl[-1]
    return x

def var_unwrap(e, fnlist, modelctx):
    if z3.is_var(e) and z3.get_var_index(e) == 0:
        fn0 = fnlist[0].as_list()
        retlist = []
        for fkey, fval in fn0[:-1]:
            retlist.append([fkey, fnmap(fval, fnlist[1:])])
        retlist.append(fnmap(fn0[-1], fnlist[1:]))
        return retlist
    if e.num_args() != 1:
        raise Exception('cannot var_unwrap: %s' % str(e))
    arg = e.arg(0)
    f = e.decl()
    return var_unwrap(arg, [modelctx[f]] + fnlist, modelctx)

def model_unwrap(e, modelctx):
    if e is None:
        return None
    if isinstance(e, z3.FuncDeclRef):
        return e.name()
    if isinstance(e, z3.IntNumRef):
        return int(e.as_long())
    if isinstance(e, z3.FuncInterp):
        elist = e.as_list()
        if len(elist) == 1 and elist[0].num_args() > 0:
            elist = var_unwrap(elist[0], [], modelctx)
        return [model_unwrap(x, modelctx) for x in elist]
    if isinstance(e, z3.BoolRef):
        return (str(e) == 'True')
    if isinstance(e, list):
        return [model_unwrap(x, modelctx) for x in e]
    if isinstance(e, z3.ExprRef) and e.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
        univ = modelctx.get_universe(e.sort())
        positions = [i for i, v in enumerate(univ) if v.eq(e)]
        if len(positions) != 1:
            raise Exception('could not find %s in %s' % (str(e), str(univ)))
        return positions[0]
    raise Exception('%s: unknown type %s' % (e, simsym.strtype(e)))

def same_assignments(model):
    # Based on http://stackoverflow.com/questions/11867611
    conds = [simsym.wrap(z3.BoolVal(True))]
    uninterp_sorts = []
    uninterp_pairs = []
    for decl in model:
        val = model[decl]
        if decl.arity() > 0:
            # Unclear what to do about functions in a model.
            continue
        # XXX hack to discard non-interesting variables
        if '!' in str(decl):
            continue
        dconst = decl()
        dsort = dconst.sort()
        if dsort in [z3.IntSort(), z3.BoolSort()]:
            conds.append(dconst == val)
        elif dsort.kind() == z3.Z3_UNINTERPRETED_SORT:
            if dsort not in uninterp_sorts: uninterp_sorts.append(dsort)
            uninterp_pairs.append((dsort, dconst, val))
        elif dsort.kind() == z3.Z3_ARRAY_SORT:
            # XXX treat arrays like uninterpreted sorts to construct
            # different initial states?
            pass
        else:
            raise Exception('unknown sort %s kind %d in %s' %
                            (dsort, dsort.kind(), decl))
    for s in uninterp_sorts:
        for k1, v1 in [(k, v) for s2, k, v in uninterp_pairs if s2 == s]:
            for k2, v2 in [(k, v) for s2, k, v in uninterp_pairs if s2 == s]:
                if v1.eq(v2):
                    conds.append(k1 == k2)
                else:
                    conds.append(k1 != k2)
    return simsym.symand(conds)

tests = [
    # (State, 3, {},
    #  [State.sys_inc, State.sys_dec, State.sys_iszero]),
    # (Pipe,  3, {},
    #  [Pipe.write, Pipe.read]),
    # (UPipe, 3, {},
    #  [UPipe.u_write, UPipe.u_read]),
    # (Fs,    2, {'first': lambda(x): x[0]},
    #  [Fs.open, Fs.read, Fs.write, Fs.unlink, Fs.link, Fs.rename]),

    (Fs, 2, {}, [
        Fs.open,
        Fs.read,
        Fs.write,
        Fs.unlink,
        Fs.link,
        Fs.rename,
        Fs.stat,
     ]),
]

parser = argparse.ArgumentParser()
parser.add_argument('-c', '--print-conds', action='store_true')
parser.add_argument('-t', '--test-file')
args = parser.parse_args()

testcases = {}
if args.test_file is None:
    testfile = None
else:
    testfile = open(args.test_file, 'w')

def print_cond(msg, cond):
    if simsym.check(cond)[0] == z3.unsat:
        return

    ## If the assumptions (i.e., calls to simsym.assume) imply the condition
    ## is true, we say that condition always holds, and we can print "always".
    ## It would be nice to print a clean condition that excludes assumptions,
    ## even if the assumptions don't directly imply the condition, but that
    ## would require finding the simplest expression for x such that
    ##
    ##   x AND simsym.assume_list = cond
    ##
    ## which seems hard to do using Z3.  In principle, this should be the
    ## same as simplifying the 'c' expression below, but Z3 isn't good at
    ## simplifying it.  We could keep the two kinds of constraints (i.e.,
    ## explicit assumptions vs. symbolic execution control flow constraints)
    ## separate in simsym, which will make them easier to disentangle..

    c = simsym.implies(simsym.symand(simsym.assume_list), cond)
    if simsym.check(simsym.symnot(c))[0] == z3.unsat:
        s = 'always'
    else:
        if args.print_conds:
            scond = simsym.simplify(cond)
            s = '\n    ' + str(scond).replace('\n', '\n    ')
        else:
            s = 'sometimes'
    print '  %s: %s' % (msg, s)

z3printer._PP.max_lines = float('inf')
for (base, ncomb, projections, calls) in tests:
    module_testcases = []

    projected_calls = list(calls)
    for p in projections:
        for c in calls:
            projected_calls.append(projected_call(p, projections[p], c))

    for callset in itertools.combinations_with_replacement(projected_calls, ncomb):
        print ' '.join([c.__name__ for c in callset])
        conds = collections.defaultdict(lambda: simsym.wrap(z3.BoolVal(False)))
        for result, cond in simsym.symbolic_apply(test, base, *callset).items():
            conds[result] = cond

        # Internal variables help deal with situations where, for the same
        # assignment of initial state + external inputs, two operations both
        # can commute and can diverge (depending on internal choice, like the
        # inode number for file creation).
        commute = conds[()]
        cannot_commute = simsym.symnot(simsym.exists(simsym.internals(), commute))

        for diverge, cond in sorted(conds.items()):
            if diverge == ():
                print_cond('can commute', cond)
            else:
                print_cond('cannot commute, %s can diverge' % ', '.join(diverge),
                           simsym.symand([cond, cannot_commute]))

        if testfile is not None:
            e = commute
            while True:
                check, model = simsym.check(e)
                if check == z3.unsat: break
                if check == z3.unknown:
                    raise Exception('Cannot enumerate: %s' % str(e))

                ## What should we do about variables that do not show up
                ## in the assignment (e.g., because they were eliminated
                ## due to combining multiple paths)?  One possibility, to
                ## generate more test cases, is to pick some default value
                ## for them (since the exact value does not matter).  Doing
                ## so will force this loop to iterate over all possible
                ## assignments, even to these "missing" variables.  Another
                ## possibility is to extract "interesting" variables from
                ## the raw symbolic expression returned by symbolic_apply().

                vars = { model_unwrap(k, model): model_unwrap(model[k], model)
                         for k in model }
                module_testcases.append({
                    'calls': [c.__name__ for c in callset],
                    'vars':  vars,
                })
                notsame = simsym.symnot(same_assignments(model))
                e = simsym.symand([e, notsame])

    print
    testcases[base.__name__] = module_testcases

if testfile is not None:
    testfile.write(json.dumps(testcases, indent=2))
