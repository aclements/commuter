import z3
import simsym
import symtypes
import errno
import model
import signal

class SFn(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Fn')

class SInum(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Inum')

class SDataByte(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('DataByte')

class SVa(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('VA')

class SPipeId(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('PipeId')

SPid = simsym.SBool
SOffset = simsym.tsynonym("SOffset", simsym.SInt)
SData = symtypes.tlist(SDataByte, lenType=SOffset)
SPipe = simsym.tstruct(data = SData,
                       nread = SOffset)
SPipeMap = symtypes.tmap(SPipeId, SPipe)
SFd = simsym.tstruct(ispipe = simsym.SBool,
                     pipeid = SPipeId,
                     pipewriter = simsym.SBool,
                     inum = SInum,
                     off = SOffset)
SFdNum = simsym.tsynonym("SFdNum", simsym.SInt)
SFdMap = symtypes.tdict(SFdNum, SFd)
SVMA = simsym.tstruct(anon = simsym.SBool,
                      writable = simsym.SBool,
                      inum = SInum,
                      off = SOffset,
                      anondata = SDataByte)
SVaMap = symtypes.tdict(SVa, SVMA)
SProc = symtypes.tstruct(fd_map = SFdMap,
                         va_map = SVaMap)
SDirMap = symtypes.tdict(SFn, SInum)
SNLink = simsym.tsynonym("SNLink", simsym.SInt)
STime = simsym.tsynonym("STime", simsym.SInt)
SInode = simsym.tstruct(data = SData,
                        nlink = SNLink,
                        atime = STime,
                        mtime = STime,
                        ctime = STime,
                        ## XXX Directories impl:
                        # isdir = simsym.SBool,
                        # dirmap = SDirMap,
                       )
SIMap = symtypes.tmap(SInum, SInode)
## XXX Directories impl:
# SPathname = simsym.tstruct(last = SFn)
## XXX Non-directories impl:
SPathname = SFn

## For some types, we override the default handling in
## IsomorphicMatch.  In particular, by default integers are treated as
## concrete-valued, but we often want to treat them as uninterpreted
## or ignore them completely.  isomorphism_types maps from Symbolic
## types to:
##
## - "ignore", if the type should be ignored altogether when
##   enumerating models.
##
## - "equal", if the type should be constrained only on equality (just
##   like an uninterpreted sort).
##
## At present, the Symbolic type can only be a primitive type or a
## synonym for a primitive type, since isomorphism will destructure
## any compound types before checking this.

isomorphism_types = {
    SNLink: "ignore",  # Unused for test generation
    SOffset: "ignore", # Too many cases in link*link (XXX maybe fixed?)
    STime: "ignore",   # Irrelevant for test generation for now
    SFdNum: "equal",
}

class Fs(model.Struct):
    __slots__ = ['i_map',
                 'proc0',
                 'proc1',
                 'pipes',

                 ## XXX Non-directories impl:
                 'root_dir',
                ]
    root_inum = SInum.any('Inum.root')

    def __init__(self):
        self.i_map = SIMap.any('Fs.imap')
        self.proc0 = SProc.any('Fs.proc0')
        self.proc1 = SProc.any('Fs.proc1')
        self.pipes = SPipeMap.any('Fs.pipes')

        ## XXX Non-directories impl:
        self.root_dir = SDirMap.any('Fs.rootdir')

    def getproc(self, pid):
        if pid == False:
            return self.proc0
        return self.proc1

    def iused(self, inum):
        dir = SInum.any('dir')
        fn = SFn.any('fn')
        fd = SFdNum.any('fd')
        pid = SPid.any('pid')

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
                simsym.symand([self.proc0.fd_map.contains(fd),
                               simsym.symnot(self.proc0.fd_map._map[fd].ispipe),
                               self.proc0.fd_map._map[fd].inum == inum])),

            simsym.exists(fd,
                simsym.symand([self.proc1.fd_map.contains(fd),
                               simsym.symnot(self.proc1.fd_map._map[fd].ispipe),
                               self.proc1.fd_map._map[fd].inum == inum])),
            ])

    def add_selfpid(self, pid):
        ## XXX hack due to our simplified PID model
        ## without loss of generality, assume syscall "a" happens in proc0
        if str(pid).startswith('a.'):
            simsym.assume(pid == False)

    def nameiparent(self, pn):
        ## XXX Non-directories impl:
        return 0, self.root_dir, pn

        ## XXX Directories impl:
        # simsym.assume(self.i_map[self.root_inum].isdir)
        # return self.root_inum, self.i_map[self.root_inum].dirmap, pn.last

    @model.methodwrap(pn=SPathname,
                      creat=simsym.SBool,
                      excl=simsym.SBool,
                      trunc=simsym.SBool,
                      anyfd=simsym.SBool,
                      pid=SPid,
                      internal_alloc_inum=SInum,
                      internal_ret_fd=SFdNum,
                      internal_time=STime,
                     )
    def open(self, pn, creat, excl, trunc, anyfd, pid,
             internal_alloc_inum, internal_ret_fd, internal_time):
        self.add_selfpid(pid)
        created = False
        anyfd = False
        _, pndirmap, pnlast = self.nameiparent(pn)
        if creat:
            if not pndirmap.contains(pnlast):
                simsym.assume(simsym.symnot(self.iused(internal_alloc_inum)))

                ## Allocating dummy variables, then assigning or asserting
                ## to/about their struct fields, and finally doing whole-struct
                ## assignment seems to be easier for Z3 than ## poking at struct
                ## members in existing large structs.
                data_empty = SData.any(simsym.anon_name('dummy_data'))
                simsym.assume(data_empty._len == 0)
                idata = SInode.any(simsym.anon_name('dummy_idata'))
                idata.data = data_empty
                idata.nlink = 1
                self.i_map[internal_alloc_inum] = idata
                pndirmap[pnlast] = internal_alloc_inum

                simsym.assume(internal_time > self.i_map[internal_alloc_inum].atime)
                simsym.assume(internal_time > self.i_map[internal_alloc_inum].mtime)
                simsym.assume(internal_time > self.i_map[internal_alloc_inum].ctime)
                self.i_map[internal_alloc_inum].atime = internal_time
                self.i_map[internal_alloc_inum].mtime = internal_time
                self.i_map[internal_alloc_inum].ctime = internal_time
                created = True
            else:
                if excl: return ('err', errno.EEXIST)
        if not pndirmap.contains(pnlast):
            return ('err', errno.ENOENT)

        inum = pndirmap[pnlast]
        if trunc:
            if not created:
                simsym.assume(internal_time > self.i_map[inum].mtime)
                simsym.assume(internal_time > self.i_map[inum].ctime)
                self.i_map[inum].mtime = internal_time
                self.i_map[inum].ctime = internal_time
            data_empty = SData.any(simsym.anon_name('dummy_data'))
            simsym.assume(data_empty._len == 0)
            self.i_map[inum].data = data_empty

        simsym.assume(internal_ret_fd >= 0)
        simsym.assume(simsym.symnot(self.getproc(pid).fd_map.contains(internal_ret_fd)))

        ## Lowest FD
        otherfd = SFdNum.any('fd')
        simsym.assume(simsym.symor([anyfd,
            simsym.symnot(simsym.exists(otherfd,
                simsym.symand([otherfd >= 0,
                               otherfd < internal_ret_fd,
                               self.getproc(pid).fd_map.contains(otherfd)])))]))

        fd_data = SFd.any(simsym.anon_name('dummy_fd_data'))
        fd_data.inum = inum
        fd_data.off = 0
        fd_data.ispipe = False
        self.getproc(pid).fd_map[internal_ret_fd] = fd_data

        return ('ok', internal_ret_fd)

    @model.methodwrap(pid=SPid,
                      internal_pipeid=SPipeId,
                      internal_fd_r=SFdNum,
                      internal_fd_w=SFdNum,
                      )
    def pipe(self, pid, internal_pipeid, internal_fd_r, internal_fd_w):
        self.add_selfpid(pid)

        xfd = SFdNum.any('xfd')
        simsym.assume(simsym.symnot(simsym.symor([
            simsym.exists(xfd,
                simsym.symand([self.proc0.fd_map.contains(xfd),
                               self.proc0.fd_map._map[xfd].ispipe,
                               self.proc0.fd_map._map[xfd].pipeid == internal_pipeid])),
            simsym.exists(xfd,
                simsym.symand([self.proc1.fd_map.contains(xfd),
                               self.proc1.fd_map._map[xfd].ispipe,
                               self.proc1.fd_map._map[xfd].pipeid == internal_pipeid]))])))

        empty_pipe = SPipe.any(simsym.anon_name('dummy_pipe'))
        empty_pipe.nread = 0
        simsym.assume(empty_pipe.data.len() == 0)
        self.pipes[internal_pipeid] = empty_pipe

        ## lowest FD for read end
        simsym.assume(internal_fd_r >= 0)
        simsym.assume(simsym.symnot(self.getproc(pid).fd_map.contains(internal_fd_r)))
        simsym.assume(simsym.symnot(simsym.exists(xfd,
                simsym.symand([xfd >= 0,
                               xfd < internal_fd_r,
                               self.getproc(pid).fd_map.contains(xfd)]))))
        fd_r_data = SFd.any(simsym.anon_name('dummy_fd_data'))
        fd_r_data.ispipe = True
        fd_r_data.pipeid = internal_pipeid
        fd_r_data.pipewriter = False
        self.getproc(pid).fd_map[internal_fd_r] = fd_r_data

        ## lowest FD for write end
        simsym.assume(internal_fd_w >= 0)
        simsym.assume(simsym.symnot(self.getproc(pid).fd_map.contains(internal_fd_w)))
        simsym.assume(simsym.symnot(simsym.exists(xfd,
                simsym.symand([xfd >= 0,
                               xfd < internal_fd_w,
                               self.getproc(pid).fd_map.contains(xfd)]))))
        fd_w_data = SFd.any(simsym.anon_name('dummy_fd_data'))
        fd_w_data.ispipe = True
        fd_w_data.pipeid = internal_pipeid
        fd_w_data.pipewriter = True
        self.getproc(pid).fd_map[internal_fd_w] = fd_w_data

        return ('ok', internal_fd_r, internal_fd_w)

    @model.methodwrap(src=SPathname, dst=SPathname,
                      internal_time=STime)
    def rename(self, src, dst, internal_time):
        srcdiri, srcdirmap, srclast = self.nameiparent(src)
        dstdiri, dstdirmap, dstlast = self.nameiparent(dst)
        if not srcdirmap.contains(srclast):
            return ('err', errno.ENOENT)
        if srcdiri == dstdiri and srclast == dstlast:
            return ('ok',)
        if dstdirmap.contains(dstlast):
            dstinum = dstdirmap[dstlast]
        else:
            dstinum = None
        dstdirmap[dstlast] = srcdirmap[srclast]
        del srcdirmap[srclast]
        if dstinum is not None:
            self.i_map[dstinum].nlink = self.i_map[dstinum].nlink - 1
            simsym.assume(internal_time > self.i_map[dstinum].ctime)
            self.i_map[dstinum].ctime = internal_time
        return ('ok',)

    @model.methodwrap(pn=SPathname, internal_time=STime)
    def unlink(self, pn, internal_time):
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        inum = dirmap[pnlast]
        del dirmap[pnlast]
        self.i_map[inum].nlink = self.i_map[inum].nlink - 1
        simsym.assume(internal_time > self.i_map[inum].ctime)
        self.i_map[inum].ctime = internal_time
        return ('ok',)

    @model.methodwrap(oldpn=SPathname, newpn=SPathname, internal_time=STime)
    def link(self, oldpn, newpn, internal_time):
        olddiri, olddirmap, oldlast = self.nameiparent(oldpn)
        newdiri, newdirmap, newlast = self.nameiparent(newpn)
        if not olddirmap.contains(oldlast):
            return ('err', errno.ENOENT)
        if newdirmap.contains(newlast):
            return ('err', errno.EEXIST)
        inum = olddirmap[oldlast]
        newdirmap[newlast] = inum
        self.i_map[inum].nlink = self.i_map[inum].nlink + 1
        simsym.assume(internal_time > self.i_map[inum].ctime)
        self.i_map[inum].ctime = internal_time
        return ('ok',)

    def iread(self, inum, off, time):
        simsym.assume(off >= 0)
        if off >= self.i_map[inum].data._len:
            return ('eof',)
        if time is not None:
            simsym.assume(time > self.i_map[inum].atime)
            self.i_map[inum].atime = time
        return ('data', self.i_map[inum].data[off])

    @model.methodwrap(fd=SFdNum, pid=SPid, internal_time=STime)
    def read(self, fd, pid, internal_time):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        if self.getproc(pid).fd_map[fd].ispipe:
            if self.getproc(pid).fd_map[fd].pipewriter:
                return ('err', errno.EBADF)
            pipe = self.pipes[self.getproc(pid).fd_map[fd].pipeid]
            if pipe.data.len() == pipe.nread:
                ## TODO: return EOF if no more writers; otherwise block
                return ('err', 0)
            simsym.assume(pipe.nread < pipe.data.len())
            simsym.assume(pipe.nread >= 0)
            d = pipe.data[pipe.nread]
            pipe.nread = pipe.nread + 1
            return ('data', d)
        off = self.getproc(pid).fd_map[fd].off
        r = self.iread(self.getproc(pid).fd_map[fd].inum, off, internal_time)
        if r[0] == 'data':
            self.getproc(pid).fd_map[fd].off = off + 1
        return r

    @model.methodwrap(fd=SFdNum, off=SOffset, pid=SPid, internal_time=STime)
    def pread(self, fd, off, pid, internal_time):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        if self.getproc(pid).fd_map[fd].ispipe:
            return ('err', errno.ESPIPE)
        return self.iread(self.getproc(pid).fd_map[fd].inum, off, internal_time)

    def iwrite(self, inum, off, databyte, time):
        simsym.assume(off >= 0)
        ## Avoid overly-long files.  fs-test.py caps file size at 16 units.
        simsym.assume(off < 10)
        ## XXX Handle sparse files?
        simsym.assume(off <= self.i_map[inum].data._len)

        if off == self.i_map[inum].data._len:
            self.i_map[inum].data.append(databyte)
        else:
            self.i_map[inum].data[off] = databyte
        if time is not None:
            simsym.assume(time > self.i_map[inum].mtime)
            simsym.assume(time > self.i_map[inum].ctime)
            self.i_map[inum].mtime = time
            self.i_map[inum].ctime = time
        return ('ok',)

    @model.methodwrap(fd=SFdNum, databyte=SDataByte, pid=SPid, internal_time=STime)
    def write(self, fd, databyte, pid, internal_time):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        if self.getproc(pid).fd_map[fd].ispipe:
            if not self.getproc(pid).fd_map[fd].pipewriter:
                return ('err', errno.EBADF)
            pipe = self.pipes[self.getproc(pid).fd_map[fd].pipeid]
            ## TODO: return EPIPE if no more readers
            simsym.assume(pipe.nread < pipe.data.len())
            simsym.assume(pipe.nread >= 0)
            pipe.data.append(databyte)
            return ('ok',)
        off = self.getproc(pid).fd_map[fd].off
        self.getproc(pid).fd_map[fd].off = off + 1
        return self.iwrite(self.getproc(pid).fd_map[fd].inum, off, databyte, internal_time)

    @model.methodwrap(fd=SFdNum, off=SOffset, databyte=SDataByte, pid=SPid, internal_time=STime)
    def pwrite(self, fd, off, databyte, pid, internal_time):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        if self.getproc(pid).fd_map[fd].ispipe:
            return ('err', errno.ESPIPE)
        return self.iwrite(self.getproc(pid).fd_map[fd].inum, off, databyte, internal_time)

    def istat(self, inum):
        len = self.i_map[inum].data._len
        nlink = self.i_map[inum].nlink
        atime = self.i_map[inum].atime
        mtime = self.i_map[inum].mtime
        ctime = self.i_map[inum].ctime
        return ('ok', inum, len, nlink, atime, mtime, ctime)

    @model.methodwrap(pn=SPathname)
    def stat(self, pn):
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        return self.istat(dirmap[pnlast])

    @model.methodwrap(fd=SFdNum, pid=SPid)
    def fstat(self, fd, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        if self.getproc(pid).fd_map[fd].ispipe:
            return ('ok', 0, 0, 0, 0, 0, 0)
        return self.istat(self.getproc(pid).fd_map[fd].inum)

    @model.methodwrap(fd=SFdNum, pid=SPid)
    def close(self, fd, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return ('err', errno.EBADF)
        del self.getproc(pid).fd_map[fd]
        return ('ok',)

    @model.methodwrap(anon=simsym.SBool,
                      writable=simsym.SBool,
                      fixed=simsym.SBool,
                      va=SVa,
                      fd=SFdNum,
                      off=SOffset,
                      pid=SPid,
                      internal_freeva=SVa)
    def mmap(self, anon, writable, fixed, va, fd, off, pid, internal_freeva):
        ## TODO: MAP_SHARED/MAP_PRIVATE for files
        ##       -> how to model delayed file read?
        ## TODO: MAP_SHARED/MAP_PRIVATE for anon (with fork)
        ## TODO: zeroing anon memory
        self.add_selfpid(pid)
        myproc = self.getproc(pid)
        if not fixed:
            va = internal_freeva
            simsym.assume(simsym.symnot(myproc.va_map.contains(va)))
        vma = SVMA.any(simsym.anon_name('dummy_vma'))
        vma.anon = anon
        vma.writable = writable
        if not anon:
            if not myproc.fd_map.contains(fd):
                return ('err', errno.EBADF)
            if myproc.fd_map[fd].ispipe:
                return ('err', errno.EACCES)
            vma.off = off
            vma.inum = myproc.fd_map[fd].inum
        myproc.va_map[va] = vma
        return ('ok', va)

    @model.methodwrap(va=SVa, pid=SPid)
    def munmap(self, va, pid):
        self.add_selfpid(pid)
        del self.getproc(pid).va_map[va]
        return ('ok',)

    @model.methodwrap(va=SVa, writable=simsym.SBool, pid=SPid)
    def mprotect(self, va, writable, pid):
        self.add_selfpid(pid)
        myproc = self.getproc(pid)
        if not myproc.va_map.contains(va):
            return ('err', errno.ENOMEM)
        myproc.va_map[va].writable = writable
        return ('ok',)

    @model.methodwrap(va=SVa, pid=SPid, internal_time=STime)
    def mem_read(self, va, pid, internal_time):
        self.add_selfpid(pid)
        myproc = self.getproc(pid)
        if not myproc.va_map.contains(va):
            return ('signal', signal.SIGSEGV)
        if myproc.va_map[va].anon:
            return ('data', myproc.va_map[va].anondata)
        ## TODO: memory-mapped reads don't bump atime?
        internal_time = None
        return self.iread(myproc.va_map[va].inum, myproc.va_map[va].off, internal_time)

    @model.methodwrap(va=SVa, databyte=SDataByte, pid=SPid, internal_time=STime)
    def mem_write(self, va, databyte, pid, internal_time):
        self.add_selfpid(pid)
        myproc = self.getproc(pid)
        if not myproc.va_map.contains(va):
            return ('signal', signal.SIGSEGV)
        if not myproc.va_map[va].writable:
            return ('signal', signal.SIGSEGV)
        if myproc.va_map[va].anon:
            myproc.va_map[va].anondata = databyte
            return ('ok',)
        ## TODO: memory-mapped writes don't bump mtime/ctime?
        internal_time = None
        return self.iwrite(myproc.va_map[va].inum, myproc.va_map[va].off,
                           databyte, internal_time)

model_class = Fs
model_functions = [
#    Fs.open,
    Fs.pipe,
    Fs.pread,
    Fs.pwrite,
    Fs.read,
    Fs.write,
    Fs.unlink,
    Fs.link,
    Fs.rename,
    Fs.stat,
    Fs.fstat,
    Fs.close,
    Fs.mmap,
    Fs.munmap,
    Fs.mprotect,
    Fs.mem_read,
    Fs.mem_write,
]
