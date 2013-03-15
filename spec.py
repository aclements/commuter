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
import time

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

## Although some things are integers, we treat them as uninterpreted
## sorts in IsomorphicMatch, by checking what decl the integer is
## being assigned to.  The first part of the tuple is the decl, and
## the second is the fake uninterpreted sort name that these values
## will be treated as.  The sort name only matters for matching up
## with other sort names in this same list.  This results in an
## approximation; see also the comment about else clause handling
## in IsomorphicMatch.

pseudo_sort_decls = [
    (SInode.__z3_sort__.nlink, 'file-nlink'),
    (SData.__z3_sort__._len, 'file-length'),
]

## Ignore some pseudo sort names altogether when enumerating models.

pseudo_sort_ignore = {
    'file-nlink': True,     ## unused for test generation
    'file-length': True,    ## too many cases in link*link
    'fd-num': False,
}

def add_pseudo_sort_decl(decl, name):
    for d, _ in pseudo_sort_decls:
        if d.eq(decl): return
    pseudo_sort_decls.append((decl, name))

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
        simsym.assume(self.data_empty._len == 0)

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

    def add_fdvar(self, fdvar):
        add_pseudo_sort_decl(simsym.unwrap(fdvar).decl(), 'fd-num')

    def add_offvar(self, offvar):
        add_pseudo_sort_decl(simsym.unwrap(offvar).decl(), 'file-length')

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
        self.add_fdvar(fd)
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
        self.add_fdvar(fd)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        off = self.fd_map[fd].off
        r = self.iread(self.fd_map[fd].inum, off)
        if r[0] == 'data':
            self.fd_map[fd].off = off + 1
        return r

    def pread(self, which):
        fd = simsym.SInt.any('Fs.pread[%s].fd' % which)
        self.add_fdvar(fd)
        off = simsym.SInt.any('Fs.pread[%s].off' % which)
        self.add_offvar(off)
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
        self.add_fdvar(fd)
        if not self.fd_map.contains(fd):
            return ('err', errno.EBADF)
        databyte = SDataByte.any('Fs.write[%s].data' % which)
        off = self.fd_map[fd].off
        self.fd_map[fd].off = off + 1
        return self.iwrite(self.fd_map[fd].inum, off, databyte)

    def pwrite(self, which):
        fd = simsym.SInt.any('Fs.pwrite[%s].fd' % which)
        self.add_fdvar(fd)
        off = simsym.SInt.any('Fs.pwrite[%s].off' % which)
        self.add_offvar(off)
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
        self.add_fdvar(fd)
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

def contains_var(expr):
    if z3.is_var(expr):
        return True
    return any([contains_var(child) for child in expr.children()])

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
    if not contains_var(e):
        return None
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
        ## Sometimes Z3 gives us assignments like:
        ##   k!21594 = [else -> k!21594!21599(k!21597(Var(0)))],
        ##   k!21597 = [Fn!val!1 -> Fn!val!1, else -> Fn!val!0],
        ##   k!21594!21599 = [Fn!val!0 -> True, else -> False],
        ## Check if elist[0] contains a Var() thing; if so, unwrap the Var.
        if len(elist) == 1:
            var_elist = var_unwrap(elist[0], [], modelctx)
            if var_elist is not None:
                elist = var_elist
        return [model_unwrap(x, modelctx) for x in elist]
    if isinstance(e, z3.BoolRef):
        if z3.is_true(e):
            return True
        if z3.is_false(e):
            return False
        raise Exception('Suspect boolean: %s' % e)
    if isinstance(e, list):
        return [model_unwrap(x, modelctx) for x in e]
    if isinstance(e, z3.ExprRef) and e.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
        univ = modelctx.get_universe(e.sort())
        positions = [i for i, v in enumerate(univ) if v.eq(e)]
        if len(positions) != 1:
            raise Exception('could not find %s in %s' % (str(e), str(univ)))
        return positions[0]
    if isinstance(e, z3.DatatypeRef):
        nc = None
        for i in range(0, e.sort().num_constructors()):
            if e.decl().eq(e.sort().constructor(i)): nc = i
        if nc is None:
            raise Exception('Could not find constructor for %s' % e)
        dict = { '_datatype_decl': e.decl().name() }
        for i in range(0, e.sort().constructor(nc).arity()):
            fieldname = str(e.sort().accessor(nc, i))
            dict[fieldname] = model_unwrap(e.arg(i), modelctx)
        return dict
    if isinstance(e, z3.ArrayRef):
        if z3.is_as_array(e):
            f = z3.get_as_array_func(e)
            return model_unwrap(modelctx[f], modelctx)
    raise Exception('%s: unknown type %s' % (e, simsym.strtype(e)))

class IsomorphicMatch(object):
    ## Originally based on http://stackoverflow.com/questions/11867611

    ## We need to construct a condition for two assignments being isomorphic
    ## to each other.  This is interesting for uninterpreted sorts, where
    ## we don't care about the specific value assignment from Z3, and care
    ## only about whether the equality pattern looks the same.  This is
    ## made more complicated by the fact that uninterpreted sorts show up
    ## all over the place: as values of a variable, as values in an array,
    ## as keys in an array, as default 'else' values in an array, etc.

    def __init__(self, model):
        self.uninterps = collections.defaultdict(list)
        self.conds = [z3.BoolVal(True)]

        # Try to reach a fixed-point with expressions of uninterpreted
        # sorts used in array indexes.
        self.groups_changed = True
        while self.groups_changed:
            self.groups_changed = False
            self.process_model(model)

        self.process_uninterp()

    def process_model(self, model):
        for decl in model:
            ## Do not bother including "internal" variables in the wrapped model;
            ## otherwise Z3 can iterate over different assignments to these
            ## variables, while we care only about assignments to "external"
            ## variables.
            if '!' in str(decl):
                continue
            self.process_decl_assignment(decl, model[decl], model)

    def process_decl_assignment(self, decl, val, model):
        if decl.arity() > 0:
            raise Exception('handle nonzero arity')

            ## Handle FuncDeclRef objects -- XXX old code.
            assert(decl.arity() == 1)

            val_list = val.as_list()
            for valarg, valval in val_list[:-1]:
                self.add_equal(decl(self.uwrap(valarg)), valval)

            domain_sorts = [decl.domain(i) for i in range(0, decl.arity())]
            domain_anon = [z3.Const(simsym.anon_name(), s) for s in domain_sorts]
            elsecond = z3.ForAll(domain_anon,
                          z3.Or([decl(*domain_anon) == self.uwrap(val_list[-1])] +
                                [domain_anon[0] == self.uwrap(x)
                                 for x, _ in val_list[:-1]]))
            self.conds.append(elsecond)
            return

        dconst = decl()
        self.process_const_assignment(dconst, val, model)

    def process_const_assignment(self, dconst, val, model):
        dsort = dconst.sort()

        if dsort.kind() == z3.Z3_DATATYPE_SORT:
            nc = None
            for i in range(0, dsort.num_constructors()):
                if val.decl().eq(dsort.constructor(i)): nc = i
            if nc is None:
                raise Exception('Could not find constructor for %s' % str(dconst))
            for i in range(0, dsort.constructor(nc).arity()):
                dconst_field = dsort.accessor(nc, i)(dconst)
                childval = val.children()[i]
                self.process_const_assignment(dconst_field, childval, model)
            return

        if dsort.kind() in [z3.Z3_INT_SORT,
                            z3.Z3_BOOL_SORT,
                            z3.Z3_UNINTERPRETED_SORT]:
            if not z3.is_const(val):
                print 'WARNING: Not a constant:', val
            self.add_assignment(dconst, val)
            return

        if dsort.kind() == z3.Z3_ARRAY_SORT:
            if z3.is_as_array(val):
                func_interp = model[z3.get_as_array_func(val)]
            else:
                func_interp = val
            assert(isinstance(func_interp, z3.FuncInterp))

            flist = func_interp.as_list()

            ## Handle Var() things; see comment in model_unwrap().
            if len(flist) == 1:
                var_flist = var_unwrap(flist[0], [], model)
                if var_flist is not None:
                    flist = var_flist

            for fidx, fval in flist[:-1]:
                fidxrep = self.uninterp_representative(fidx)
                if fidxrep is None: continue
                self.process_const_assignment(dconst[fidxrep], fval, model)

            ## One problem is what to do with ArrayRef assignments (in the form of
            ## a FuncInterp), because FuncInterp assigns a value for every index,
            ## but we only care about specific indexes.  (It's not useful to receive
            ## another model that differs only in some index we never cared about.)
            ## To deal with this problem, we add FuncInterp constraints only for
            ## indexes that are interesting.  For uninterpreted sorts, this
            ## is the universe of values for that sort.  For interpreted sorts
            ## (integers), we add constraints for values explicitly listed in
            ## the FuncInterp, and skip the "else" clause altogether.  This is
            ## imprecise: it means self.conds is less constrained than it should
            ## be, so its negation is too strict, and might preclude some
            ## otherwise-interesting assignments.

            if dconst.domain().kind() == z3.Z3_UNINTERPRETED_SORT:
                for idx in model.get_universe(dconst.domain()):
                    if any([idx.eq(i) for i, _ in flist[:-1]]): continue
                    idxrep = self.uninterp_representative(idx)
                    if idxrep is None: continue
                    self.process_const_assignment(dconst[idxrep], flist[-1], model)
            return

        print dsort.kind()
        raise Exception('handle %s = %s' % (dconst, val))

    def uninterp_groups(self, sort):
        groups = []
        for expr, val in self.uninterps[sort]:
            found = False
            for group_val, group_exprs in groups:
                if val.eq(group_val):
                    group_exprs.append(expr)
                    found = True
            if not found:
                groups.append((val, [expr]))
        return groups

    def uninterp_representative(self, val):
        for expr2, val2 in self.uninterps[val.sort()]:
            if val.eq(val2):
                return expr2
        return None

    def add_assignment(self, expr, val):
        sort = val.sort()
        if sort.kind() == z3.Z3_UNINTERPRETED_SORT:
            self.add_assignment_uninterp(expr, val, sort)
            return

        for d, sortname in pseudo_sort_decls:
            if not expr.decl().eq(d): continue
            if pseudo_sort_ignore[sortname]: return
            self.add_assignment_uninterp(expr, val, sortname)
            return

        if expr.sort().kind() != z3.Z3_BOOL_SORT:
            print 'WARNING: Interpreted sort assignment:', expr, val

        cond = (expr == val)
        if not any([c.eq(cond) for c in self.conds]):
            self.conds.append(cond)

    def add_assignment_uninterp(self, expr, val, sort):
        new_group = True
        for uexpr, uval in self.uninterps[sort]:
            if uval.eq(val):
                new_group = False
                if uexpr.eq(expr): return
        if new_group:
            self.groups_changed = True
        self.uninterps[sort].append((expr, val))

    def process_uninterp(self):
        for sort in self.uninterps:
            groups = self.uninterp_groups(sort)
            for _, exprs in groups:
                for otherexpr in exprs[1:]:
                    self.conds.append(exprs[0] == otherexpr)
            representatives = [exprs[0] for _, exprs in groups]
            if len(representatives) > 1:
                self.conds.append(z3.Distinct(representatives))

    def notsame_cond(self):
        return simsym.wrap(z3.Not(z3.And(self.conds)))

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

## Timestamp keeps track of generated test cases (a poor nonce)
testcases = { '__gen_ts': int(time.time()) }
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
        for result, condlist in simsym.symbolic_apply(test, base, *callset).items():
            conds[result] = condlist

        # Internal variables help deal with situations where, for the same
        # assignment of initial state + external inputs, two operations both
        # can commute and can diverge (depending on internal choice, like the
        # inode number for file creation).
        commute = simsym.symor(conds[()])
        cannot_commute = simsym.symnot(simsym.exists(simsym.internals(), commute))

        for diverge, condlist in sorted(conds.items()):
            if diverge == ():
                print_cond('can commute', simsym.symor(condlist))
            else:
                print_cond('cannot commute, %s can diverge' % ', '.join(diverge),
                           simsym.symand([simsym.symor(condlist), cannot_commute]))

        if testfile is not None:
            for e in conds[()]:
                ## This can potentially reduce the number of test cases
                ## by, e.g., eliminating irrelevant variables from e.
                ## The effect doesn't seem significant: one version of Fs
                ## produces 3204 test cases without simplify, and 3182 with.
                e = simsym.simplify(e)
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
                             for k in model
                             if '!' not in model_unwrap(k, model) }
                    # print 'New assignment:', vars
                    module_testcases.append({
                        'calls': [c.__name__ for c in callset],
                        'vars':  vars,
                    })

                    same = IsomorphicMatch(model)
                    notsame = same.notsame_cond()
                    # print 'Negation:', notsame
                    e = simsym.symand([e, notsame])

    print
    testcases[base.__name__] = module_testcases

if testfile is not None:
    testfile.write(json.dumps(testcases, indent=2))
