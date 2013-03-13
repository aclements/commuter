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
    SItembag = symtypes.tbag(simsym.SInt)

    def __init__(self):
        self.elems = self.SItembag.any('UPipe.items')
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
            e = self.elems.take()
            self.nitem = self.nitem - 1
            return e

class SFn(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Fn')

class SInum(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Inum')

class SDataByte(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('DataByte')

SData = symtypes.tlist(SDataByte)
SFd = simsym.tstruct(inum = SInum, off = simsym.SInt)
SFdMap = symtypes.tdict(simsym.SInt, SFd)
SDirMap = symtypes.tdict(SFn, SInum)
SInode = simsym.tstruct(data = SData,
                        nlink = simsym.SInt,
                        ## XXX Directories impl:
                        # isdir = simsym.SBool,
                        # dirmap = SDirMap,
                       )
SIMap = symtypes.tmap(SInum, SInode)
## XXX Directories impl:
# SPathname = simsym.tstruct(last = SFn)
## XXX Non-directories impl:
SPathname = SFn

class Fs(Struct):
    __slots__ = ['i_map',
                 'fd_map',
                 'data_empty',

                 ## XXX Non-directories impl:
                 'root_dir',
                ]
    root_inum = SInum.any('Inum.root')

    def __init__(self):
        self.i_map = SIMap.any('Fs.imap')
        self.fd_map = SFdMap.any('Fs.fdmap')
        self.data_empty = SData.any('Data.empty')
        self.data_empty._len = 0

        ## XXX Non-directories impl:
        self.root_dir = SDirMap.any('Fs.rootdir')

    def iused(self, inum):
        dir = SInum.any('dir')
        fn = SFn.any('fn')
        fd = simsym.SInt.any('fd')

        # If we try to simply index into dirmap, its __getitem__
        # won't have access to the supposition that it contains the right
        # key, and throw an exception.  Thus, we use _map directly.
        return simsym.symor([
            ## XXX Directories impl:
            # simsym.exists(dir,
            #     simsym.symand([
            #         self.i_map[dir].isdir,
            #         simsym.exists(fn,
            #             simsym.symand([self.i_map[dir].dirmap.contains(fn),
            #                            self.i_map[dir].dirmap._map[fn] == inum]))])),

            ## XXX Non-directories impl:
            simsym.exists(fn,
                simsym.symand([self.root_dir.contains(fn),
                               self.root_dir._map[fn] == inum])),

            simsym.exists(fd,
                simsym.symand([self.fd_map.contains(fd),
                               self.fd_map._map[fd].inum == inum]))])

    def nameiparent(self, pn):
        ## XXX Non-directories impl:
        return 0, self.root_dir, pn

        ## XXX Directories impl:
        # simsym.assume(self.i_map[self.root_inum].isdir)
        # return self.root_inum, self.i_map[self.root_inum].dirmap, pn.last

    def open(self, which):
        pn = SPathname.any('Fs.open[%s].pn' % which)
        creat = simsym.SBool.any('Fs.open[%s].creat' % which)
        excl = simsym.SBool.any('Fs.open[%s].excl' % which)
        trunc = simsym.SBool.any('Fs.open[%s].trunc' % which)
        anyfd = simsym.SBool.any('Fs.open[%s].anyfd' % which)
        _, pndirmap, pnlast = self.nameiparent(pn)
        if creat:
            if not pndirmap.contains(pnlast):
                inum = SInum.any('Fs.open[%s].ialloc' % which)
                simsym.add_internal(inum)
                simsym.assume(simsym.symnot(self.iused(inum)))

                idata = SInode.any()
                idata.data = self.data_empty
                idata.nlink = 1
                self.i_map[inum] = idata
                pndirmap[pnlast] = inum
            else:
                if excl: return ('err', errno.EEXIST)
        if not pndirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        if trunc:
            self.i_map[pndirmap[pnlast]].data = self.data_empty

        fd = simsym.SInt.any('Fs.open[%s].fd' % which)
        simsym.add_internal(fd)
        simsym.assume(fd >= 0)
        simsym.assume(simsym.symnot(self.fd_map.contains(fd)))

        ## Lowest FD
        otherfd = simsym.SInt.any()
        simsym.assume(simsym.symor([anyfd,
            simsym.symnot(simsym.exists(otherfd,
                simsym.symand([otherfd >= 0,
                               otherfd < fd,
                               self.fd_map.contains(otherfd)])))]))

        fd_data = SFd.any()
        fd_data.inum = pndirmap[pnlast]
        fd_data.off = 0
        self.fd_map[fd] = fd_data

        return ('ok', fd)

    def rename(self, which):
        src = SPathname.any('Fs.rename[%s].src' % which)
        dst = SPathname.any('Fs.rename[%s].dst' % which)
        srcdiri, srcdirmap, srclast = self.nameiparent(src)
        dstdiri, dstdirmap, dstlast = self.nameiparent(dst)
        if srcdiri == dstdiri and srclast == dstlast:
            return ('ok',)
        if not srcdirmap.contains(srclast):
            return ('err', errno.ENOENT)
        if dstdirmap.contains(dstlast):
            dstinum = dstdirmap[dstlast]
        else:
            dstinum = None
        dstdirmap[dstlast] = srcdirmap[srclast]
        del dstdirmap[dstlast]
        if dstinum is not None:
            self.i_map[dstinum].nlink = self.i_map[dstinum].nlink - 1
        return ('ok',)

    def unlink(self, which):
        pn = SPathname.any('Fs.unlink[%s].fn' % which)
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        inum = dirmap[pnlast]
        del dirmap[pnlast]
        self.i_map[inum].nlink = self.i_map[inum].nlink - 1
        return ('ok',)

    def link(self, which):
        oldpn = SPathname.any('Fs.link[%s].old' % which)
        newpn = SPathname.any('Fs.link[%s].new' % which)
        olddiri, olddirmap, oldlast = self.nameiparent(oldpn)
        newdiri, newdirmap, newlast = self.nameiparent(newpn)
        if not olddirmap.contains(oldlast):
            return ('err', errno.ENOENT)
        if newdirmap.contains(newlast):
            return ('err', errno.EEXIST)
        inum = olddirmap[oldlast]
        newdirmap[newlast] = inum
        self.i_map[inum].nlink = self.i_map[inum].nlink + 1
        return ('ok',)

    def iread(self, inum, off):
        simsym.assume(off >= 0)
        if off >= self.i_map[inum].data._len:
            return ('eof',)
        return ('data', self.i_map[inum].data[off])

    def read(self, which):
        fd = simsym.SInt.any('Fs.read[%s].fd' % which)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        off = self.fd_map[fd].off
        r = self.iread(self.fd_map[fd].inum, off)
        if r[0] == 'data':
            self.fd_map[fd].off = off + 1
        return r

    def pread(self, which):
        fd = simsym.SInt.any('Fs.pread[%s].fd' % which)
        off = simsym.SInt.any('Fs.pread[%s].off' % which)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        return self.iread(self.fd_map[fd].inum, off)

    def iwrite(self, inum, off, databyte):
        simsym.assume(off >= 0)
        ## XXX Handle sparse files?
        simsym.assume(off <= self.i_map[inum].data._len)

        if off == self.i_map[inum].data._len:
            self.i_map[inum].data.append(databyte)
        else:
            self.i_map[inum].data[off] = databyte
        return ('ok',)

    def write(self, which):
        fd = simsym.SInt.any('Fs.write[%s].fd' % which)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        databyte = SDataByte.any('Fs.write[%s].data' % which)
        off = self.fd_map[fd].off
        self.fd_map[fd].off = off + 1
        return self.iwrite(self.fd_map[fd].inum, off, databyte)

    def pwrite(self, which):
        fd = simsym.SInt.any('Fs.pwrite[%s].fd' % which)
        off = simsym.SInt.any('Fs.pwrite[%s].off' % which)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        databyte = SDataByte.any('Fs.pwrite[%s].databyte' % which)
        return self.iwrite(self.fd_map[fd].inum, off, databyte)

    def istat(self, inum):
        len = self.i_map[inum].data._len
        nlink = self.i_map[inum].nlink
        return ('ok', inum, len, nlink)

    def stat(self, which):
        pn = SPathname.any('Fs.stat[%s].fn' % which)
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        return self.istat(dirmap[pnlast])

    def fstat(self, which):
        fd = simsym.SInt.any('Fs.fstat[%s].fd' % which)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        return self.istat(self.fd_map[fd].inum)

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

        ## XXX precisely keeping track of what diverges incurs overhead.
        ## Avoid the needless book-keeping for now.
        if len(diverge) == 0: return ()
        return ('something',)

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
        # if len(elist) == 1 and elist[0].num_args() > 0:
        #     elist = var_unwrap(elist[0], [], modelctx)
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
    if isinstance(e, z3.DatatypeRef):
        return [e.decl().name()] + [model_unwrap(e.arg(i), modelctx)
                             for i in range(0, e.num_args())]
    if isinstance(e, z3.ArrayRef):
        if z3.is_as_array(e):
            f = z3.get_as_array_func(e)
            return model_unwrap(modelctx[f], modelctx)
    raise Exception('%s: unknown type %s' % (e, simsym.strtype(e)))

def same_assignments(model):
    # Based on http://stackoverflow.com/questions/11867611
    conds = [simsym.wrap(z3.BoolVal(True))]
    uninterp_sorts = []
    uninterp_pairs = []
    for decl in model:
        val = model[decl]
        if '!' in str(decl):
            ## Do not mention internal variables in the same_assignments
            ## condition, otherwise Z3 just happily keeps iterating on
            ## these non-interesting variables to produce effectively
            ## identical assignments.
            continue
        if decl.arity() > 0:
            val_list = val.as_list()
            for valarg, valval in val_list[:-1]:
                conds.append(decl(valarg) == valval)

            domain_sorts = [decl.domain(i) for i in range(0, decl.arity())]
            domain_anon = [z3.Const(simsym.anon_name(), s) for s in domain_sorts]
            elsecond = z3.ForAll(domain_anon,
                          z3.Or([decl(*domain_anon) == val_list[-1]] +
                                [domain_anon[0] == x for x, _ in val_list[:-1]]))
            conds.append(elsecond)
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
        elif dsort.kind() == z3.Z3_DATATYPE_SORT:
            if dsort.num_constructors() != 1:
                raise Exception('Too many constructors for data type %s' % dsort)
                conds.append(dconst == val)

            constructor = dsort.constructor(0)
            c_arity = constructor.arity()
            for i in range(0, c_arity):
                childval = val.children()[i]
                dconst_field = dsort.accessor(0, i)(dconst)
                if not z3.is_as_array(childval):
                    cond = (dconst_field == childval)
                    conds.append(cond)
                else:
                    var = z3.get_as_array_func(childval)
                    childval = model[var]
                    assert(isinstance(childval, z3.FuncInterp))

                    val_list = childval.as_list()
                    for valarg, valval in val_list[:-1]:
                        cond = dconst_field[valarg] == valval
                        conds.append(cond)

                    domain_anon = z3.Const(simsym.anon_name(), dconst_field.domain())
                    elsecond = z3.ForAll(domain_anon,
                                  z3.Or([dconst_field[domain_anon] == val_list[-1]] +
                                        [domain_anon == x for x, _ in val_list[:-1]]))
                    conds.append(elsecond)
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
    # (UPipe, 2, {},
    #  [UPipe.u_write, UPipe.u_read]),
    # (Fs,    2, {'first': lambda(x): x[0]},
    #  [Fs.open, Fs.read, Fs.write, Fs.unlink, Fs.link, Fs.rename]),

    (Fs, 2, {}, [
        Fs.open,
        Fs.pread,
        Fs.pwrite,
        Fs.read,
        Fs.write,
        Fs.unlink,
        Fs.link,
        Fs.rename,
        Fs.stat,
        Fs.fstat,
     ]),
]

parser = argparse.ArgumentParser()
parser.add_argument('-c', '--check-conds', action='store_true')
parser.add_argument('-p', '--print-conds', action='store_true')
parser.add_argument('-t', '--test-file')
args = parser.parse_args()

testcases = {}
if args.test_file is None:
    testfile = None
else:
    testfile = open(args.test_file, 'w')

def print_cond(msg, cond):
    if args.check_conds and simsym.check(cond)[0] == z3.unsat:
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
    if args.check_conds and simsym.check(simsym.symnot(c))[0] == z3.unsat:
        s = 'always'
    else:
        if args.print_conds:
            scond = simsym.simplify(cond)
            s = '\n    ' + str(scond).replace('\n', '\n    ')
        else:
            if args.check_conds:
                s = 'sometimes'
            else:
                s = 'maybe'
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
                    # raise Exception('Cannot enumerate: %s' % str(e))
                    print 'Cannot enumerate, moving on..'
                    print 'Failure reason:', model
                    break

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
                         for k in model if '!' not in model_unwrap(k, model) }
                # print 'New assignment:', vars
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
