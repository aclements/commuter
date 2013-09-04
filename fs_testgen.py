import testgen
import simsym
import collections
import fs as fs_module

all_filenames = ['__f%d' % x for x in range(0, 6)]

fd_begin = 10
fd_end = 20

pipe_begin = 20   ## even is reader, odd is writer
pipe_end = 30

# This must be kept in sync with fstest.cc
va_base = 0x12345600000
va_len = 4

# const char * expressions for referring to datavals.  Each DataVal is
# DATAVAL_BYTES, where the first byte is unique and the rest are
# zeros.
DataVal = collections.namedtuple('DataVal', 'expr first_byte')
all_datavals = [DataVal('dataval%d' % i, i) for i in range(8)]

class SkipTest(Exception):
  pass

class PerProc(object):
  def __init__(self):
    assert(fd_begin > 3)
    # Map from SFdNum to concrete FD number
    self.fds = testgen.DynamicDict(range(fd_begin, fd_end))
    # Map from SVa to concrete virtual address
    self.vas = testgen.DynamicDict((va_base + i * 4096) for i in range(va_len))

class Inode(object):
  def __init__(self, num):
    self.fname = '__i%d' % num

class FsState(object):
  def __init__(self, fs):
    self.fs = fs
    # Map from uninterpreted path names to concrete file names
    self.filenames = testgen.DynamicDict(all_filenames)
    # Map from SInum to concrete Inode object
    self.inums = testgen.DynamicDict(map(Inode, range(0, 6)))
    # Map from SDataVal to DataVal
    self.datavals = testgen.DynamicDict(all_datavals)
    # Map from uninterpreted pipe IDs to reader FDs (writers are +1)
    self.pipes = testgen.DynamicDict(range(pipe_begin, pipe_end, 2))
    self.procs = testgen.DynamicDict(iter(PerProc, None))

  def build_proc(self, pid):
    fdmap = {}
    proc = self.fs.proc1 if pid else self.fs.proc0
    for symfd, fd in self.procs[pid].fds.items():
      if not proc.fd_map.contains(symfd):
        continue
      fdmap[fd] = proc.fd_map[symfd]
    vamap = {}
    for symva, va in self.procs[pid].vas.items():
      if not proc.va_map.contains(symva):
        continue
      vamap[va] = proc.va_map[symva]
    return (fdmap, vamap)

  def setup_inodes(self):
    def writen(fdexpr, data):
      alen = data.len()
      assert 0 <= alen <= 16
      if alen == 0:
        return
      for i in range(alen):
        emit('r = write(%s, %s, %d);' % (fdexpr, self.datavals[data[i]].expr,
                                         DATAVAL_BYTES),
             'if (r != %d) setup_error("write => %%d", r);' % DATAVAL_BYTES)

    emit = self.emit
    emit('int fd __attribute__((unused));',
         'int fds[2] __attribute__((unused));',
         'int r __attribute__((unused));',
         'char c __attribute__((unused));')
    for syminum, inode in self.inums.items():
      emit('fd = open("%s", O_CREAT | O_TRUNC | O_RDWR, 0666);' % inode.fname,
           'if (fd < 0) setup_error("open");')

      syminode = self.fs.i_map[syminum]
      if syminode is not None:
        writen('fd', syminode.data)

      emit('close(fd);')

    for pipeid, reader_fd in self.pipes.items():
      writer_fd = reader_fd + 1
      emit('r = pipe2(fds, O_NONBLOCK);',
           'if (r != 0) setup_error("pipe => %d", r);',
           'r = dup2(fds[0], %d);' % reader_fd,
           'if (r != %d) setup_error("dup2");' % reader_fd,
           'r = dup2(fds[1], %d);' % writer_fd,
           'if (r != %d) setup_error("dup2");' % writer_fd)
      sympipe = self.fs.pipes[pipeid]
      writen('fds[1]', sympipe.data)
      emit('close(fds[0]);',
           'close(fds[1]);')

  def setup_filenames(self, fn_to_ino):
    for fn in fn_to_ino:
      self.emit('r = link("%s", "%s");' % (fn_to_ino[fn].fname, fn),
                'if (r < 0) setup_error("link");')

  def setup_inodes_finalize(self):
    for inode in self.inums.values():
      self.emit('unlink("%s");' % inode.fname)
    for reader_fd in self.pipes.values():
      writer_fd = reader_fd + 1
      self.emit('close(%d);' % reader_fd,
                'close(%d);' % writer_fd)

  def setup_proc(self, fdmap, vamap):
    emit = self.emit
    emit('int fd __attribute__((unused));',
         'int r __attribute__((unused));')
    for fd, fdinfo in fdmap.items():
      if fdinfo.ispipe:
        pipe_setup_fd = self.pipes[fdinfo.pipeid]
        if fdinfo.pipewriter: pipe_setup_fd += 1
        emit('r = dup2(%d, %d);' % (pipe_setup_fd, fd),
             'if (r < 0) setup_error("dup2");')
      else:
        emit('fd = open("%s", O_RDWR);' % self.inums[fdinfo.inum].fname,
             'if (fd < 0) setup_error("open");',
             'r = lseek(fd, %d, SEEK_SET);' % (fdinfo.off * DATAVAL_BYTES),
             'if (fd >= 0 && r < 0) setup_error("lseek");',
             'r = dup2(fd, %d);' % fd,
             'if (fd >= 0 && r < 0) setup_error("dup2");',
             'close(fd);')

    emit('char* va __attribute__((unused));')
    for va, vainfo in vamap.items():
      emit('va = (void*) %#xUL;' % va)
      prot = 'PROT_READ'
      if vainfo.writable:
        prot += ' | PROT_WRITE'
      if vainfo.anon:
        emit('r = (intptr_t)mmap(va, 4096, %s, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);' % prot,
             'if (r == -1) setup_error("mmap");')
        if vainfo.writable:
          emit('*va = %d;' % self.datavals[vainfo.anondata].first_byte)
        else:
          emit('*(volatile int*)va;')
      else:
        emit('fd = open("%s", O_RDWR);' % self.inums[vainfo.inum].fname,
             'if (fd < 0) setup_error("open");',
             'r = (intptr_t)mmap(va, 4096, %s, MAP_SHARED | MAP_FIXED, fd, %#xUL);' % (prot, vainfo.off * PAGE_BYTES),
             'if (r == -1) setup_error("mmap");',
             'close(fd);')

  def setup_proc_finalize(self):
    for reader_fd in self.pipes.values():
      writer_fd = reader_fd + 1
      self.emit('close(%d);' % reader_fd,
                'close(%d);' % writer_fd)

  def build_dir(self):
    # Reads filenames; extends inums
    fn_to_ino = {}
    for symfn, fn in self.filenames.items():
      if not self.fs.root_dir.contains(symfn):
        continue
      syminum = self.fs.root_dir[symfn]
      fn_to_ino[fn] = self.inums[syminum]

    # Reads procs[pid].fds and procs[pid].vas; extends nothing
    (fdmap0, vamap0) = self.build_proc(False)
    (fdmap1, vamap1) = self.build_proc(True)

    setup = {'common': testgen.CodeWriter(),
             'proc0': testgen.CodeWriter(),
             'proc1': testgen.CodeWriter(),
             'procfinal': testgen.CodeWriter(),
             'final': testgen.CodeWriter()}

    try:
      # setup_proc reads nothing; extends inums, datavals, pipes
      self.emit = setup['proc0']; self.setup_proc(fdmap0, vamap0)
      self.emit = setup['proc1']; self.setup_proc(fdmap1, vamap1),
      # setup_inodes reads inums, pipes; extends datavals
      self.emit = setup['common']; self.setup_inodes()
      # setup_filenames reads nothing; extends nothing
      self.emit = setup['common']; self.setup_filenames(fn_to_ino)
      # setup_proc_finalize reads pipes; extends nothing
      self.emit = setup['procfinal']; self.setup_proc_finalize()
      # setup_inodes_finalize reads inums, pipes; extends nothing
      self.emit = setup['final']; self.setup_inodes_finalize()
    finally:
      self.emit = None
    return setup

  def gen_code(self, callname, args, res):
    f = getattr(self, callname)
    self.emit = writer = testgen.CodeWriter()
    try:
      f(args, res.copy())
    finally:
      self.emit = None
    return writer

  def __check(self, res):
    """Return code to check the expected values of res.

    res must be a dictionary mapping variable names to expected
    values.  'errno' and DataVals are handled specially.
    """
    emit = testgen.CodeWriter()
    for var, val in res.items():
      if var == 'errno':
        continue
      if isinstance(val, DataVal):
        emit('expect_result("%s", %s[0], %d);' % (var, var, val.first_byte))
      else:
        emit('expect_result("%s", %s, %d);' % (var, var, val))
    if 'errno' in res:
      emit('expect_errno(%d);' % res['errno'])
    return emit

  def open(self, args, res):
    flags = ['O_RDWR']
    if args.excl:
      flags.append('O_EXCL')
    if args.creat:
      flags.append('O_CREAT')
    if args.trunc:
      flags.append('O_TRUNC')
    if args.anyfd:
      flags.append('O_ANYFD')
    if res['r'] >= 0:
      # XXX Can we match up the symbolic FD with the real FD?
      del res['r']
    self.emit(
      'int r = open("%s", %s, 0666);' %
      (self.filenames[args.pn], ' | '.join(flags)),
      self.__check(res),
      'return xerrno(r);')

  def pipe(self, args, res):
    if res['r'] >= 0:
      # XXX Match up FDs?
      del res['fds[0]'], res['fds[1]']
    self.emit(
      'int fds[2];',
      'int r = pipe(fds);',
      self.__check(res),
      'return xerrno(r);')

  def pread(self, args, res):
    if 'data' in res:
      res['data'] = self.datavals[res['data']]
    self.emit(
      'char *data = datavalbuf;',
      'ssize_t r = pread(%d, data, %d, %d);' % \
      (self.procs[args.pid].fds[args.fd], DATAVAL_BYTES,
       args.off * DATAVAL_BYTES),
      self.__check(res),
      'if (r <= 0) return xerrno(r);',
      'return data[0];')

  def pwrite(self, args, res):
    self.emit(
      'ssize_t r = pwrite(%d, %s, %d, %d);' % \
      (self.procs[args.pid].fds[args.fd], self.datavals[args.databyte].expr,
       DATAVAL_BYTES, args.off * DATAVAL_BYTES),
      self.__check(res),
      'return xerrno(r);')

  def read(self, args, res):
    if 'data' in res:
      res['data'] = self.datavals[res['data']]
    self.emit(
      'char *data = datavalbuf;',
      'ssize_t r = read(%d, data, %d);' % \
      (self.procs[args.pid].fds[args.fd], DATAVAL_BYTES),
      self.__check(res),
      'if (r < 0) return xerrno(r);',
      'return data[0];')

  def write(self, args, res):
    self.emit(
      'ssize_t r = write(%d, %s, %d);' % \
      (self.procs[args.pid].fds[args.fd], self.datavals[args.databyte].expr,
       DATAVAL_BYTES),
      self.__check(res),
      'if (r <= 0) return xerrno(r);',
      'return r;')

  def unlink(self, args, res):
    self.emit(
      'int r = unlink("%s");' % self.filenames[args.pn],
      self.__check(res),
      'return xerrno(r);')

  def link(self, args, res):
    self.emit(
      'int r = link("%s", "%s");' % (self.filenames[args.oldpn],
                                     self.filenames[args.newpn]),
      self.__check(res),
      'return xerrno(r);')

  def rename(self, args, res):
    self.emit(
      'int r = rename("%s", "%s");' % (self.filenames[args.src],
                                       self.filenames[args.dst]),
      self.__check(res),
      'return xerrno(r);')

  def __prune_stat_res(self, res):
    # XXX We could match some of these results up with their
    # concrete values
    for field in ['st.st_ino', 'st.st_nlink', 'st.st_atime', 'st.st_mtime',
                  'st.st_ctime']:
      if field in res:
        del res[field]

  def stat(self, args, res):
    self.__prune_stat_res(res)
    self.emit(
      'struct stat st;',
      'int r = stat("%s", &st);' % self.filenames[args.pn],
      self.__check(res),
      'if (r < 0) return xerrno(r);',
      '/* Hack, to test for approximate equality */',
      'return st.st_ino ^ st.st_nlink ^ st.st_size;')

  def fstat(self, args, res):
    self.__prune_stat_res(res)
    self.emit(
      'struct stat st;',
      'int r = fstat(%d, &st);' % self.procs[args.pid].fds[args.fd],
      self.__check(res),
      'if (r < 0) return xerrno(r);',
      '/* Hack, to test for approximate equality */',
      'return st.st_ino ^ st.st_nlink ^ st.st_size;')

  def close(self, args, res):
    self.emit(
      'int r = close(%d);' % self.procs[args.pid].fds[args.fd],
      self.__check(res),
      'return xerrno(r);')

  def lseek(self, args, res):
    self.emit(
      'int r = lseek(%d, %d, %s);' %
      (self.procs[args.pid].fds[args.fd],
       args.off * DATAVAL_BYTES,
       'SEEK_SET' if args.whence_set else
       'SEEK_CUR' if args.whence_cur else
       'SEEK_END' if args.whence_end else '999'),
      self.__check(res),
      'return xerrno(r);')

  def mmap(self, args, res):
    prot = 'PROT_READ'
    if args.writable: prot += ' | PROT_WRITE'

    if args.anon:
      flags = 'MAP_PRIVATE | MAP_ANONYMOUS'
    else:
      flags = 'MAP_SHARED'

    if args.fixed:
      flags += ' | MAP_FIXED'
      va = self.procs[args.pid].vas[args.va]
    else:
      va = 0

    if 'r:va' in res:
      if args.fixed:
        res['r'] = self.procs[args.pid].vas[res['r:va']]
      del res['r:va']

    self.emit(
      'int* va = (int*) %#xUL;' % va,
      'long r = (intptr_t) mmap(va, 4096, %s, %s, %d, %#xUL);' %
      (prot, flags, self.procs[args.pid].fds[args.fd], args.off * PAGE_BYTES),
      self.__check(res),
      'return xerrno(r);')

  def munmap(self, args, res):
    self.emit(
      'int* va = (int*) %#xUL;' % self.procs[args.pid].vas[args.va],
      'int r = munmap(va, 4096);',
      self.__check(res),
      'return xerrno(r);')

  def mprotect(self, args, res):
    prot = 'PROT_READ'
    if args.writable:
      prot += ' | PROT_WRITE'
    self.emit(
      'int* va = (int*) %#xUL;' % self.procs[args.pid].vas[args.va],
      'int r = mprotect(va, 4096, %s);' % prot,
      self.__check(res),
      'return xerrno(r);')

  def memread(self, args, res):
    if 'r:data' in res:
      res['r'] = self.datavals[res.pop('r:data')].first_byte
    self.emit(
      'char* p = (char*) %#xUL;' % self.procs[args.pid].vas[args.va],
      'int r, signal;',
      'pf_active = 1;',
      'if ((signal = sigsetjmp(pf_jmpbuf, 1)))',
      '  r = -1;',
      'else',
      '  r = *p;',
      'pf_active = 0;',
      self.__check(res),
      'return r;')

  def memwrite(self, args, res):
    self.emit(
      'char* p = (char*) %#xUL;' % self.procs[args.pid].vas[args.va],
      'int signal, r = 0;',
      'pf_active = 1;',
      'if ((signal = sigsetjmp(pf_jmpbuf, 1)))',
      '  r = -1;',
      'else',
      '  *p = %d;' % self.datavals[args.databyte].first_byte,
      'pf_active = 0;',
      self.__check(res),
      'return r;')

class FsTestGenerator(testgen.TestGenerator):
  def __init__(self, test_file_name):
    super(FsTestGenerator, self).__init__(test_file_name)
    self.emit = testgen.CodeWriter(open(test_file_name, 'w'))
    self.fstests = []
    self.pathid = self.modelno = None
    self.__funcs = {}
    self.__pending_funcs = {}

    # Get some constants from fs
    global DATAVAL_BYTES, PAGE_BYTES
    DATAVAL_BYTES = fs_module.DATAVAL_BYTES
    PAGE_BYTES = fs_module.PAGE_BYTES

    self.emit("""\
//+++ common
#define _GNU_SOURCE 1
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <setjmp.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include "fstest.h"
""")

    # Generate datavals
    for i, d in enumerate(all_datavals):
      self.emit("__attribute__((__weak__)) const char %s[%d] = {%d};" %
                (d.expr, DATAVAL_BYTES, d.first_byte))
    # Create a buffer for datavals.  This is in the BSS, so we'll
    # touch it after fork (unlike, say, if it were on the stack).
    self.emit("__attribute__((__weak__)) char datavalbuf[%d];" % DATAVAL_BYTES)
    self.emit()

    self.emit("//+++ tests")

  def begin_path(self, result):
    super(FsTestGenerator, self).begin_path(result)
    self.pathid = result.pathid
    self.modelno = 0

  def func(self, emit, ret, fname, body):
    key = (ret, str(body))
    existing = self.__funcs.get(key)
    code = 'static %s %s(void) {\n%s\n}' % (ret, fname, body.indent())
    if existing is None:
      self.__pending_funcs[key] = fname
      emit(code)
      return fname
    else:
      # Put the original body in as a comment for readability
      emit(testgen.CodeWriter()(code).indent('// '))
      emit('// ^ See %s' % existing)
      return existing

  def on_model(self, model):
    super(FsTestGenerator, self).on_model(model)

    name = "%s_%s_%d" % ("_".join(self.callset_names), self.pathid,
                         self.modelno)

    emit = testgen.CodeWriter()
    self.__pending_funcs.clear()

    try:
      emit("""\

/*
 * calls: %s
 */""" % " ".join(self.callset_names))
      fs = FsState(model['Fs'])
      pids = []
      fns = {}
      for callidx, callname in enumerate(self.callset_names):
        # Generate test code for this call.  As a side-effect, this will
        # fill in structures we need to write the setup code.
        args = self.get_call_args(callidx)
        res = {k: self.eval(v) for k, v in self.get_result(callidx).items()}
        fns['test_%d' % callidx] \
          = self.func(emit, 'int', 'test_%s_%d' % (name, callidx),
                      fs.gen_code(callname, args, res))
        if hasattr(args, 'pid'):
          pids.append(args.pid)
        else:
          # Some calls don't take a pid because their process doesn't matter
          pids.append(False)
      # Write setup code
      setup = fs.build_dir()
      for phase in ('common', 'proc0', 'proc1', 'final', 'procfinal'):
        fns['setup_' + phase] \
          = self.func(emit, 'void', 'setup_%s_%s' % (name, phase),
                      setup[phase])
    except SkipTest as e:
      print "Skipping test %s: %s" % (name, e)
      return

    # Commit to this code
    self.__funcs.update(self.__pending_funcs)
    self.emit(emit)

    strargs = {'name' : name,
               'pid0' : pids[0], 'pid1' : pids[1],
               'name0' : self.callset_names[0],
               'name1' : self.callset_names[1]}
    strargs.update(fns)
    self.fstests.append("""\
  { "fs-%(name)s",
    &%(setup_common)s,
    { { &%(setup_proc0)s }, { &%(setup_proc1)s } },
    &%(setup_procfinal)s,
    &%(setup_final)s,
    { { &%(test_0)s, %(pid0)d, "%(name0)s" },
      { &%(test_1)s, %(pid1)d, "%(name1)s" } },
    &cleanup }""" % strargs)

    self.modelno += 1

  def end_path(self):
    super(FsTestGenerator, self).end_path()
    self.pathid = self.modelno = None

  def finish(self):
    super(FsTestGenerator, self).finish()

    emit = self.emit

    # Generate cleanup code
    emit('',
         '//+++ common',
         'static void cleanup(void) {')
    for fn in all_filenames:
      emit('  unlink("%s");' % fn)
    emit('}')

    # Generate test array
    emit('', 'struct fstest fstests[] = {',
         '//+++ tests',
         '\n'.join('%s,' % x for x in self.fstests),
         '//+++ common',
         '  {}',
         '};')
