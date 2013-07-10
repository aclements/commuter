import testgen
import z3
import z3util
import simsym

class DynamicDict(object):
  """A dynamically-filled dictionary.

  Values for dictionary mappings are drawn from an iterable as they
  are needed.  This has special support for Z3 constants, making it
  useful for assigning concrete values to uninterpreted constants.

  A DynamicDict can be iterated over just like a regular dict, but
  doing so freezes its contents to prevent further additions.
  """

  def __init__(self, iterable):
    self.__gen = iter(iterable)
    self.__map = {}

  def __getitem__(self, key):
    """Return the value associated with key.

    If the dictionary does not currently contain a value for key, one
    will be drawn from self's iterable.  key may be a Z3 constant.
    """

    hkey = z3util.HashableAst(key)

    if hkey not in self.__map:
      if isinstance(key, simsym.Symbolic) and \
         not z3.is_const(simsym.unwrap(key)):
        # There's nothing wrong with supporting arbitrary ASTs, but in
        # every place we use DynamicDict, this indicates an
        # easy-to-miss bug.
        raise ValueError("Key is not a constant: %r" % key)

      if self.__gen is None:
        raise ValueError("DynamicDict has been read; cannot be extended")
      try:
        self.__map[hkey] = self.__gen.next()
      except StopIteration:
        raise ValueError("Ran out of values for %r" % key)
    return self.__map[hkey]

  def keys(self):
    self.__gen = None
    return (hkey.ast for hkey in self.__map.iterkeys())
  __iter__ = keys

  def values(self):
    self.__gen = None
    return self.__map.itervalues()

  def items(self):
    self.__gen = None
    return ((hkey.ast, val) for hkey, val in self.__map.iteritems())

all_filenames = ['__f%d' % x for x in range(0, 6)]

fd_begin = 5
fd_end = 10

va_base = 0x12345600000
va_len = 4

class SkipTest(Exception):
  pass

class PerProc(object):
  def __init__(self):
    assert(fd_begin > 3)
    self.fds = DynamicDict(range(fd_begin, fd_end))
    self.vas = DynamicDict((va_base + i * 4096) for i in range(va_len))

class FsState(object):
  def __init__(self, fs):
    self.fs = fs
    # Map from uninterpreted path names to concrete file names
    self.filenames = DynamicDict(all_filenames)
    # Map from uninterpreted inodes to inode file names
    self.inodefiles = DynamicDict(['__i%d' % x for x in range(0, 6)])
    # Map from uninterpreted data bytes to concrete byte values
    self.databytes = DynamicDict(xrange(256))
    self.procs = DynamicDict(iter(PerProc, None))

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
    emit = self.emit
    emit('int fd __attribute__((unused));',
         'int r __attribute__((unused));',
         'char c __attribute__((unused));')
    for symino, ifn in self.inodefiles.items():
      emit('fd = open("%s", O_CREAT | O_TRUNC | O_RDWR, 0666);' % ifn,
           'if (fd < 0) setup_error("open");')

      inode = self.fs.i_map[symino]
      if inode is not None:
        len = inode.data.len()
        assert 0 <= len <= 16
        ## XXX
        ## We may want to implement each Databyte as a separate 4KB page,
        ## to check for scalability of writes to different pages (as opposed
        ## to writes to different bytes, which is less interesting).

        for i in range(0, len):
          emit('c = %d;' % self.databytes[inode.data[i]],
               'r = write(fd, &c, 1);',
               'if (r != 1) setup_error("write => %d", r);')

      emit('close(fd);')

  def setup_filenames(self, fn_to_ino):
    for fn in fn_to_ino:
      self.emit('r = link("%s", "%s");' % (fn_to_ino[fn], fn),
                'if (r < 0) setup_error("link");')

  def setup_inodes_finalize(self):
    for inodefile in self.inodefiles.values():
      self.emit('unlink("%s");' % inodefile)

  def setup_proc(self, fdmap, vamap):
    emit = self.emit
    emit('int fd __attribute__((unused));',
         'int r __attribute__((unused));')
    for fd, fdinfo in fdmap.items():
      if fdinfo.ispipe:
        # XXX Support pipes
        raise SkipTest("Unimplemented: pipe FDs")
      emit('fd = open("%s", O_RDWR);' % self.inodefiles[fdinfo.inum],
           'if (fd < 0) setup_error("open");',
           'r = lseek(fd, %d, SEEK_SET);' % fdinfo.off,
           'if (fd >= 0 && r < 0) setup_error("lseek");',
           'r = dup2(fd, %d);' % fd,
           'if (fd >= 0 && r < 0) setup_error("dup2");',
           'close(fd);')

    emit('int* va __attribute__((unused));')
    for va, vainfo in vamap.items():
      emit('va = (void*) 0x%lxUL;' % va)
      prot = 'PROT_READ'
      if vainfo.writable:
        prot += ' | PROT_WRITE'
      if vainfo.anon:
        emit('r = (intptr_t)mmap(va, 4096, %s, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);' % prot,
             'if (r == -1) setup_error("mmap");')
        if vainfo.writable:
          emit('*va = %d;' % self.databytes[vainfo.anondata])
        else:
          emit('*(volatile int*)va;')
      else:
        emit('fd = open("%s", O_RDWR);' % self.inodefiles[vainfo.inum],
             'if (fd < 0) setup_error("open");',
             'r = (intptr_t)mmap(va, 4096, %s, MAP_SHARED | MAP_FIXED, fd, %d * 4096);' % (prot, vainfo.off),
             'if (r == -1) setup_error("mmap");',
             'r = mprotect(va, 4096, %s);' % prot,
             'if (r < 0) setup_error("mprotect");',
             'close(fd);')

  def build_dir(self):
    # Reads filenames; extends inodefiles
    fn_to_ino = {}
    for symfn, fn in self.filenames.items():
      if not self.fs.root_dir.contains(symfn):
        continue
      symino = self.fs.root_dir[symfn]
      fn_to_ino[fn] = self.inodefiles[symino]

    # Reads procs[pid].fds and procs[pid].vas; extends nothing
    (fdmap0, vamap0) = self.build_proc(False)
    (fdmap1, vamap1) = self.build_proc(True)

    setup = {'common': testgen.CodeWriter(),
             'proc0': testgen.CodeWriter(),
             'proc1': testgen.CodeWriter(),
             'final': testgen.CodeWriter()}

    try:
      # setup_proc reads nothing; extends inodefiles, databytes
      self.emit = setup['proc0']; self.setup_proc(fdmap0, vamap0)
      self.emit = setup['proc1']; self.setup_proc(fdmap1, vamap1),
      # setup_inodes reads inodefiles; extends databytes
      self.emit = setup['common']; self.setup_inodes()
      # setup_filenames reads nothing; extends nothing
      self.emit = setup['common']; self.setup_filenames(fn_to_ino)
      # setup_inodes_finalize reads inodefiles; extends nothing
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
    values.  'errno' is handled specially.
    """
    emit = testgen.CodeWriter()
    for var, val in res.items():
      if var == 'errno':
        continue
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
      res['data'] = self.databytes[res['data']]
    self.emit(
      'char data;',
      'ssize_t r = pread(%d, &data, 1, %d);' %
      (self.procs[args.pid].fds[args.fd], args.off),
      self.__check(res),
      'if (r <= 0) return xerrno(r);',
      'return data;')

  def pwrite(self, args, res):
    self.emit(
      'char data = %d;' % self.databytes[args.databyte],
      'ssize_t r = pwrite(%d, &data, 1, %d);' % \
      (self.procs[args.pid].fds[args.fd], args.off),
      self.__check(res),
      'return xerrno(r);')

  def read(self, args, res):
    if 'data' in res:
      res['data'] = self.databytes[res['data']]
    self.emit(
      'char data;',
      'ssize_t r = read(%d, &data, 1);' % self.procs[args.pid].fds[args.fd],
      self.__check(res),
      'if (r < 0) return xerrno(r);',
      'return data;')

  def write(self, args, res):
    self.emit(
      'char data = %d;' % self.databytes[args.databyte],
      'ssize_t r = write(%d, &data, 1);' % self.procs[args.pid].fds[args.fd],
      self.__check(res),
      'if (r <= 0) return xerrno(r);',
      'return data;')

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
      'int* va = (int*) 0x%lxUL;' % va,
      'long r = (intptr_t) mmap(va, 4096, %s, %s, %d, 0x%lxUL * 4096);' %
      (prot, flags, self.procs[args.pid].fds[args.fd], args.off),
      self.__check(res),
      'return xerrno(r);')

  def munmap(self, args, res):
    self.emit(
      'int* va = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va],
      'int r = munmap(va, 4096);',
      self.__check(res),
      'return xerrno(r);')

  def mprotect(self, args, res):
    prot = 'PROT_READ'
    if args.writable:
      prot += ' | PROT_WRITE'
    self.emit(
      'int* va = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va],
      'int r = mprotect(va, 4096, %s);' % prot,
      self.__check(res),
      'return xerrno(r);')

  def mem_read(self, args, res):
    if 'r:data' in res:
      res['r'] = self.databytes[res.pop('r:data')]
    self.emit(
      'char* p = (char*) 0x%lxUL;' % self.procs[args.pid].vas[args.va],
      'int r, signal;',
      'pf_active = 1;',
      'if ((signal = sigsetjmp(pf_jmpbuf, 1)))',
      '  r = -1;',
      'else',
      '  r = *p;',
      'pf_active = 0;',
      self.__check(res),
      'return r;')

  def mem_write(self, args, res):
    self.emit(
      'char* p = (char*) 0x%lxUL;' % self.procs[args.pid].vas[args.va],
      'int signal, r = 0;',
      'pf_active = 1;',
      'if ((signal = sigsetjmp(pf_jmpbuf, 1)))',
      '  r = -1;',
      'else',
      '  *p = %d;' % self.databytes[args.databyte],
      'pf_active = 0;',
      self.__check(res),
      'return r;')

class FsTestGenerator(testgen.TestGenerator):
  def __init__(self, test_file_name):
    super(FsTestGenerator, self).__init__(test_file_name)
    self.emit = testgen.CodeWriter(open(test_file_name, 'w'))
    self.fstests = []
    self.pathid = self.modelno = None
    self.__bodies = {}
    self.__pending_bodies = {}

    self.emit("""\
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

#ifndef XV6_USER
#define O_ANYFD 0
#endif

static int __attribute__((unused)) xerrno(int r) {
#ifdef XV6_USER
  return r;
#else
  if (r < 0)
    return -errno;
  else
    return r;
#endif
}""")

  def begin_path(self, result):
    super(FsTestGenerator, self).begin_path(result)
    self.pathid = result.pathid
    self.modelno = 0

  def func(self, emit, ret, fname, body):
    key = (ret, str(body))
    existing = self.__bodies.get(key)
    emit('static %s %s(void) {' % (ret, fname))
    if existing is None:
      self.__pending_bodies[key] = fname
      emit(body.indent())
    else:
      # Put the original body in as a comment for readability
      emit(body.indent('// ').indent())
      # Call the equivalent function
      if ret == 'void':
        emit('  %s();' % existing)
      else:
        emit('  return %s();' % existing)
    emit('}')

  def on_model(self, model):
    super(FsTestGenerator, self).on_model(model)

    name = "%s_%s_%d" % ("_".join(self.callset_names), self.pathid,
                         self.modelno)

    emit = testgen.CodeWriter()

    try:
      emit("""\

/*
 * calls: %s
 */""" % " ".join(self.callset_names))
      fs = FsState(model['Fs'])
      pids = []
      for callidx, callname in enumerate(self.callset_names):
        # Generate test code for this call.  As a side-effect, this will
        # fill in structures we need to write the setup code.
        args = self.get_call_args(callidx)
        res = {k: self.eval(v) for k, v in self.get_result(callidx).items()}
        self.func(emit, 'int', 'test_%s_%d' % (name, callidx),
                  fs.gen_code(callname, args, res))
        if hasattr(args, 'pid'):
          pids.append(args.pid)
        else:
          # Some calls don't take a pid because their process doesn't matter
          pids.append(False)
      # Write setup code
      setup = fs.build_dir()
      for phase in ('common', 'proc0', 'proc1', 'final'):
        self.func(emit, 'void',  'setup_%s_%s' % (name, phase),
                  setup[phase])
    except SkipTest as e:
      print "Skipping test %s: %s" % (name, e)
      return

    # Commit to this code
    self.__bodies.update(self.__pending_bodies)
    self.__pending_bodies.clear()
    self.emit(emit)
    self.fstests.append("""\
  { "fs-%(name)s",
    &setup_%(name)s_common,
    { { &setup_%(name)s_proc0 }, { &setup_%(name)s_proc1 } },
    &setup_%(name)s_final,
    { { &test_%(name)s_0, %(pid0)d, "%(name0)s" },
      { &test_%(name)s_1, %(pid1)d, "%(name1)s" } },
    &cleanup }""" % {'name' : name,
                     'pid0' : pids[0], 'pid1' : pids[1],
                     'name0' : self.callset_names[0],
                     'name1' : self.callset_names[1]})

    self.modelno += 1

  def end_path(self):
    super(FsTestGenerator, self).end_path()
    self.pathid = self.modelno = None

  def finish(self):
    super(FsTestGenerator, self).finish()

    emit = self.emit

    # Generate cleanup code
    emit('', 'static void cleanup(void) {')
    for fn in all_filenames:
      emit('  unlink("%s");' % fn)
    emit('}')

    # Generate test array
    emit('', 'struct fstest fstests[] = {',
         '\n'.join('%s,' % x for x in self.fstests),
         '  {}',
         '};')
