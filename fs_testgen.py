import testgen
import z3

class DynamicDict(object):
  """A dynamically-filled dictionary.

  Values for dictionary mappings are drawn from an iterable as they
  are needed.  This has special support for Z3 constants, making it
  useful for assigning concrete values to uninterpreted constants.
  """

  def __init__(self, iterable):
    self.__gen = iter(iterable)
    self.__map = {}
    self.__keys = []

  def __getitem__(self, key):
    """Return the value associated with key.

    If the dictionary does not currently contain a value for key, one
    will be drawn from self's iterable.  key may be a Z3 constant.
    """

    if z3.is_const(key):
      idx = str(key)
    else:
      idx = key

    if idx not in self.__map:
      try:
        self.__map[idx] = self.__gen.next()
      except StopIteration:
        raise ValueError("Ran out of values for %r" % key)
      self.__keys.append((key, idx))
    return self.__map[idx]

  def keys(self):
    return (real for real, _ in self.__keys)
  __iter__ = keys

  def values(self):
    return (self.__map[idx] for _, idx in self.__keys)

  def items(self):
    return ((real, self.__map[idx]) for real, idx in self.__keys)

all_filenames = ['__f%d' % x for x in range(0, 6)]

fd_begin = 5
fd_end = 10

va_base = 0x12345600000
va_len = 4

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
      fd_state = proc.fd_map[symfd]
      fdmap[fd] = { 'ino': self.inodefiles[fd_state.inum],
                    'off': fd_state.off }
    vamap = {}
    for symva, va in self.procs[pid].vas.items():
      if not proc.va_map.contains(symva):
        continue
      va_state = proc.va_map[symva]
      vamap[va] = { 'ino': self.inodefiles[va_state.inum],
                    'off': va_state.off,
                    'anon': va_state.anon,
                    'anondata': va_state.anondata,
                    'writable': va_state.writable }
    return (fdmap, vamap)

  def setup_inodes(self):
    ccode = ''
    ccode += '\n  int fd __attribute__((unused));'
    ccode += '\n  char c __attribute__((unused));'
    for symino, ifn in self.inodefiles.items():
      ccode += '\n  fd = open("%s", O_CREAT | O_TRUNC | O_RDWR, 0666);' % ifn

      inode = self.fs.i_map[symino]
      if inode is not None:
        len = inode.data.len()
        if len < 0:
          ## XXX hack -- maybe fix spec.py?
          len = 0
        if len > 16:
          ## XXX hack -- maybe fix spec.py?
          len = 16
        ## XXX
        ## We may want to implement each Databyte as a separate 4KB page,
        ## to check for scalability of writes to different pages (as opposed
        ## to writes to different bytes, which is less interesting).

        for i in range(0, len):
          ccode += '\n  c = %d;' % self.databytes[inode.data[i]]
          ccode += '\n  write(fd, &c, 1);'

      ccode += '\n  close(fd);'
    return ccode

  def setup_filenames(self, fn_to_ino):
    ccode = ''
    for fn in fn_to_ino:
      ccode += '\n  link("%s", "%s");' % (fn_to_ino[fn], fn)
    return ccode

  def setup_inodes_finalize(self):
    ccode = '' 
    for inodefile in self.inodefiles.values():
      ccode += '\n  unlink("%s");' % inodefile
    return ccode

  def setup_proc(self, fdmap, vamap):
    ccode = ''
    ccode += '\n  int fd __attribute__((unused));'
    for fd in fdmap:
      ccode += '\n  fd = open("%s", O_RDWR);' % fdmap[fd]['ino']
      ccode += '\n  lseek(fd, %d, SEEK_SET);' % fdmap[fd]['off']
      ccode += '\n  dup2(fd, %d);' % fd
      ccode += '\n  close(fd);'

    ccode += '\n  int* va __attribute__((unused));'
    for va in vamap:
      ccode += '\n  va = (void*) 0x%lxUL;' % va
      prot = 'PROT_READ'
      if vamap[va]['writable']:
        prot += ' | PROT_WRITE'
      if vamap[va]['anon']:
        ccode += '\n  mmap(va, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);'
        ccode += '\n  *va = %d;' % self.databytes[vamap[va]['anondata']]
      else:
        ccode += '\n  fd = open("%s", O_RDWR);' % vamap[va]['ino']
        ccode += '\n  mmap(va, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_FIXED, fd, %d * 4096);' % \
                 vamap[va]['off']
        ccode += '\n  mprotect(va, 4096, %s);' % prot
        ccode += '\n  close(fd);'
    return ccode

  def build_dir(self):
    fn_to_ino = {}
    for symfn, fn in self.filenames.items():
      if not self.fs.root_dir.contains(symfn):
        continue
      symino = self.fs.root_dir[symfn]
      fn_to_ino[fn] = self.inodefiles[symino]

    (fdmap0, vamap0) = self.build_proc(False)
    (fdmap1, vamap1) = self.build_proc(True)

    return {'common': self.setup_inodes() + self.setup_filenames(fn_to_ino),
            'proc0': self.setup_proc(fdmap0, vamap0),
            'proc1': self.setup_proc(fdmap1, vamap1),
            'final': self.setup_inodes_finalize(),
           }

  def gen_code(self, callname, args):
    f = getattr(self, callname)
    return f(args)

  def open(self, args):
    flags = ['O_RDWR']
    if args.excl:
      flags.append('O_EXCL')
    if args.creat:
      flags.append('O_CREAT')
    if args.trunc:
      flags.append('O_TRUNC')
    if args.anyfd:
      flags.append('O_ANYFD')
    ccode = ''
    ccode += '\n  int r = open("%s", %s, 0666);' % \
             (self.filenames[args.pn], ' | '.join(flags))
    ccode += '\n  return xerrno(r);'
    return ccode

  def pread(self, args):
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = pread(%d, &c, 1, %d);' % \
             (self.procs[args.pid].fds[args.fd], args.off)
    ccode += '\n  if (cc <= 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def pwrite(self, args):
    ccode = ''
    ccode += '\n  char c = %d;' % self.databytes[args.databyte]
    ccode += '\n  ssize_t cc = pwrite(%d, &c, 1, %d);' % \
             (self.procs[args.pid].fds[args.fd], args.off)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def read(self, args):
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = read(%d, &c, 1);' % \
             self.procs[args.pid].fds[args.fd]
    ccode += '\n  if (cc <= 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def write(self, args):
    ccode = ''
    ccode += '\n  char c = %d;' % self.databytes[args.databyte]
    ccode += '\n  ssize_t cc = write(%d, &c, 1);' % \
             self.procs[args.pid].fds[args.fd]
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def unlink(self, args):
    ccode = ''
    ccode += '\n  int r = unlink("%s");' % self.filenames[args.pn]
    ccode += '\n  return xerrno(r);'
    return ccode

  def link(self, args):
    ccode = ''
    ccode += '\n  int r = link("%s", "%s");' % (self.filenames[args.oldpn],
                                                self.filenames[args.newpn])
    ccode += '\n  return xerrno(r);'
    return ccode

  def rename(self, args):
    ccode = ''
    ccode += '\n  int r = rename("%s", "%s");' % (self.filenames[args.src],
                                                  self.filenames[args.dst])
    ccode += '\n  return xerrno(r);'
    return ccode

  def stat(self, args):
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = stat("%s", &st);' % self.filenames[args.pn]
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

  def fstat(self, args):
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = fstat(%d, &st);' % self.procs[args.pid].fds[args.fd]
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

  def close(self, args):
    ccode = ''
    ccode += '\n  int r = close(%d);' % self.procs[args.pid].fds[args.fd]
    ccode += '\n  return xerrno(r);'
    return ccode

  def mmap(self, args):
    prot = 'PROT_READ'
    if args.writable: prot += ' | PROT_WRITE'

    if args.anon:
      flags = 'MAP_PRIVATE | MAP_ANONYMOUS'
    else:
      flags = 'MAP_SHARED'

    va = self.procs[args.pid].vas[args.va]
    if args.fixed:
      flags += ' | MAP_FIXED'
    else:
      va = 0

    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % va
    ccode += '\n  return (intptr_t) mmap(va, 4096, %s, %s, %d, 0x%lxUL);' % \
             (prot, flags, self.procs[args.pid].fds[args.fd], args.off)
    return ccode

  def munmap(self, args):
    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va]
    ccode += '\n  return munmap(va, 4096);'
    return ccode

  def mprotect(self, args):
    prot = 'PROT_READ'
    if args.writable:
      prot += ' | PROT_WRITE'
    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va]
    ccode += '\n  return mprotect(va, 4096, %s);' % prot
    return ccode

  def mem_read(self, args):
    ccode = ''
    ccode += '\n  int* p = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va]
    ccode += '\n  if (sigsetjmp(pf_jmpbuf, 1))'
    ccode += '\n    return -1;'
    ccode += '\n  pf_active = 1;'
    ccode += '\n  return *p;'
    return ccode

  def mem_write(self, args):
    ccode = ''
    ccode += '\n  int* p = (int*) 0x%lxUL;' % self.procs[args.pid].vas[args.va]
    ccode += '\n  if (sigsetjmp(pf_jmpbuf, 1))'
    ccode += '\n    return -1;'
    ccode += '\n  pf_active = 1;'
    ccode += '\n  *p = %d;' % self.databytes[args.databyte]
    ccode += '\n  return 0;'
    return ccode

class FsTestGenerator(testgen.TestGenerator):
  def __init__(self, test_file_name):
    super(FsTestGenerator, self).__init__(test_file_name)
    self.test_file = open(test_file_name, 'w')
    self.fstests = []

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

  def emit(self, *code):
    self.test_file.write("\n".join(code) + "\n")

  def on_model(self, result, model):
    super(FsTestGenerator, self).on_model(result, model)

    emit = self.emit
    tidx = len(self.fstests)

    # XXX Include some information so a user can track it back to the model
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
      code = fs.gen_code(callname, args)
      if hasattr(args, 'pid'):
        pids.append(args.pid)
      else:
        # Some calls don't take a pid because their process doesn't matter
        pids.append(False)
      emit("""\
static int test_%d_%d(void) {%s
}""" % (tidx, callidx, code))
    # Write setup code
    setup = fs.build_dir()
    for phase in ('common', 'proc0', 'proc1', 'final'):
      emit("""\
static void setup_%d_%s(void) {%s
}""" % (tidx, phase, setup[phase]))
    self.test_file.flush()

    self.fstests.append("""\
  { "%(name)s",
    &setup_%(tidx)d_common,
    { { &setup_%(tidx)d_proc0 }, { &setup_%(tidx)d_proc1 } },
    &setup_%(tidx)d_final,
    { { &test_%(tidx)d_0, %(pid0)d, "%(name0)s" },
      { &test_%(tidx)d_1, %(pid1)d, "%(name1)s" } },
    &cleanup }""" % {'name' : 'fs-%d' % tidx,
                     'tidx' : tidx,
                     'pid0' : pids[0], 'pid1' : pids[1],
                     'name0' : self.callset_names[0],
                     'name1' : self.callset_names[1]})

  def finish(self):
    emit = self.emit

    # Generate cleanup code
    emit('', 'static void cleanup(void) {')
    for fn in all_filenames:
      emit('  unlink("%s");' % fn)
    emit('}')

    # Generate test array
    emit('', 'struct fstest fstests[] = {',
         ',\n'.join(self.fstests),
         '};')

    self.test_file.close()
