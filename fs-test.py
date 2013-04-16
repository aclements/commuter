import json
import sys
import os
import struct
import errno
import itertools
import collections

class SetAllocator(object):
  def __init__(self, values):
    self.avail = list(reversed(values))
    self.map = {}

  def get(self, v):
    if v not in self.map:
      self.map[v] = self.avail.pop()
    return self.map[v]

  def assigned(self):
    return self.map.keys()

all_filenames = ['__f%d' % x for x in range(0, 6)]

fd_begin = 5
fd_end = 10
all_fds = range(fd_begin, fd_end)
assert(fd_begin > 3)

va_base = 0x12345600
va_len = 4
all_vas = range(va_base, va_base + va_len)

def array_lookup_raw(array, idx):
  for k, v in array[:-1]:
    if idx == k: return v
  return array[-1]

class FsState(object):
  def __init__(self, vars):
    self.vars = vars
    self.filenames = SetAllocator(all_filenames)
    self.inodefiles = SetAllocator(['__i%d' % x for x in range(0, 6)])
    self.fds = { False: SetAllocator(all_fds),
                 True:  SetAllocator(all_fds) }
    self.vas = { False: SetAllocator(all_vas),
                 True:  SetAllocator(all_vas) }

  def array_lookup(self, arraynamechain, idx, defval):
    array = self.vars
    for name in arraynamechain:
      if name not in array: return defval
      array = array[name]
    return array_lookup_raw(array, idx)

  def get_fn(self, v):
    return self.filenames.get(v)

  def get_ifn(self, v):
    return self.inodefiles.get(v)

  def get_fd(self, pid, v):
    return self.fds[pid].get(v)

  def get_va(self, pid, v):
    return self.vas[pid].get(v) * 4096

  def build_proc(self, pid, procname):
    fdmap = {}
    for fd_idx in self.fds[pid].assigned():
      if not self.array_lookup((procname, 'fd_map', '_valid'), fd_idx, False):
        continue
      fd_state = self.array_lookup((procname, 'fd_map', '_map'), fd_idx, 0)
      fdmap[self.get_fd(pid, fd_idx)] = { 'ino': self.get_ifn(fd_state['inum']),
                                          'off': fd_state['off'] }
    vamap = {}
    for va_idx in self.vas[pid].assigned():
      if not self.array_lookup((procname, 'va_map', '_valid'), va_idx, False):
        continue
      va_state = self.array_lookup((procname, 'va_map', '_map'), va_idx, 0)
      vamap[self.get_va(pid, va_idx)] = { 'ino': self.get_ifn(va_state['inum']),
                                          'off': va_state['off'],
                                          'anon': va_state['anon'],
                                          'anondata': va_state['anondata'],
                                          'writable': va_state['writable'] }
    return (fdmap, vamap)

  def setup_inodes(self):
    ccode = ''
    ccode += '\n  int fd __attribute__((unused));'
    ccode += '\n  char c __attribute__((unused));'
    for ino_idx in self.inodefiles.assigned():
      ifn = self.get_ifn(ino_idx)
      ccode += '\n  fd = open("%s", O_CREAT | O_TRUNC | O_RDWR, 0666);' % ifn

      inode = self.array_lookup(('Fs.imap',), ino_idx, None)
      if inode is not None:
        len = inode['data']['_len']
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
          ccode += '\n  c = %d;' % array_lookup_raw(inode['data']['_vals'], i)
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
    for ino_idx in self.inodefiles.assigned():
      ccode += '\n  unlink("%s");' % self.get_ifn(ino_idx)
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
        ccode += '\n  mmap(va, 4096, %s, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);' % prot
        ccode += '\n  *va = %d;' % vamap[va]['anondata']
      else:
        ccode += '\n  fd = open("%s", O_RDWR);' % vamap[va]['ino']
        ccode += '\n  mmap(va, 4096, %s, MAP_SHARED | MAP_ANONYMOUS, fd, %d * 4096);' % \
                 (prot, vamap[va]['off'])
        ccode += '\n  close(fd);'
    return ccode

  def build_dir(self):
    fn_to_ino = {}
    for fn_idx in self.filenames.assigned():
      if not self.array_lookup(('Fs.rootdir', '_valid'), fn_idx, False):
        continue
      ino_idx = self.array_lookup(('Fs.rootdir', '_map'), fn_idx, 0)
      fn_to_ino[self.get_fn(fn_idx)] = self.get_ifn(ino_idx)

    (fdmap0, vamap0) = self.build_proc(False, 'Fs.proc0')
    (fdmap1, vamap1) = self.build_proc(True,  'Fs.proc1')

    return {'common': self.setup_inodes() + self.setup_filenames(fn_to_ino),
            'proc0': self.setup_proc(fdmap0, vamap0),
            'proc1': self.setup_proc(fdmap1, vamap1),
            'final': self.setup_inodes_finalize(),
           }

  def gen_code(self, m, which):
    pid = self.vars.get('%s.%s.pid' % (which, m), False)
    f = getattr(self, m)
    return {'pid': pid,
            'code': f(which, pid),
           }

  def open(self, which, pid):
    fn_idx = self.vars['%s.open.pn' % which]
    flags = ['O_RDWR']
    if self.vars.get('%s.open.excl' % which, False):
      flags.append('O_EXCL')
    if self.vars.get('%s.open.creat' % which, False):
      flags.append('O_CREAT')
    if self.vars.get('%s.open.trunc' % which, False):
      flags.append('O_TRUNC')
    if self.vars.get('%s.open.anyfd' % which, False):
      flags.append('O_ANYFD')
    ccode = ''
    ccode += '\n  int r = open("%s", %s, 0666);' % (self.get_fn(fn_idx),
                                                    ' | '.join(flags))
    ccode += '\n  return xerrno(r);'
    return ccode

  def pread(self, which, pid):
    fd_idx = self.vars['%s.pread.fd' % which]
    off = self.vars.get('%s.pread.off' % which, 0)
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = pread(%d, &c, 1, %d);' % (self.get_fd(pid, fd_idx), off)
    ccode += '\n  if (cc <= 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def pwrite(self, which, pid):
    fd_idx = self.vars['%s.pwrite.fd' % which]
    off = self.vars.get('%s.pwrite.off' % which, 0)
    val = self.vars.get('%s.pwrite.databyte' % which, 0)
    ccode = ''
    ccode += '\n  char c = %d;' % val
    ccode += '\n  ssize_t cc = pwrite(%d, &c, 1, %d);' % (self.get_fd(pid, fd_idx), off)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def read(self, which, pid):
    fd_idx = self.vars['%s.read.fd' % which]
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = read(%d, &c, 1);' % self.get_fd(pid, fd_idx)
    ccode += '\n  if (cc <= 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def write(self, which, pid):
    fd_idx = self.vars['%s.write.fd' % which]
    val = self.vars.get('%s.write.databyte' % which, 0)
    ccode = ''
    ccode += '\n  char c = %d;' % val
    ccode += '\n  ssize_t cc = write(%d, &c, 1);' % self.get_fd(pid, fd_idx)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def unlink(self, which, pid):
    fn_idx = self.vars['%s.unlink.pn' % which]
    ccode = ''
    ccode += '\n  int r = unlink("%s");' % self.get_fn(fn_idx)
    ccode += '\n  return xerrno(r);'
    return ccode

  def link(self, which, pid):
    oldfn_idx = self.vars.get('%s.link.oldpn' % which, 0)
    newfn_idx = self.vars.get('%s.link.newpn' % which, 0)
    ccode = ''
    ccode += '\n  int r = link("%s", "%s");' % (self.get_fn(oldfn_idx),
                                                self.get_fn(newfn_idx))
    ccode += '\n  return xerrno(r);'
    return ccode

  def rename(self, which, pid):
    srcfn_idx = self.vars.get('%s.rename.src' % which, 0)
    dstfn_idx = self.vars.get('%s.rename.dst' % which, 0)
    ccode = ''
    ccode += '\n  int r = rename("%s", "%s");' % (self.get_fn(srcfn_idx),
                                                  self.get_fn(dstfn_idx))
    ccode += '\n  return xerrno(r);'
    return ccode

  def stat(self, which, pid):
    fn_idx = self.vars['%s.stat.pn' % which]
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = stat("%s", &st);' % self.get_fn(fn_idx)
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

  def fstat(self, which, pid):
    fd_idx = self.vars['%s.fstat.fd' % which]
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = fstat(%d, &st);' % self.get_fd(pid, fd_idx)
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

  def close(self, which, pid):
    fd_idx = self.vars['%s.close.fd' % which]
    ccode = ''
    ccode += '\n  int r = close(%d);' % self.get_fd(pid, fd_idx)
    ccode += '\n  return xerrno(r);'
    return ccode

  def mmap(self, which, pid):
    va_idx = self.vars.get('%s.mmap.va' % which, 0)
    writable = self.vars.get('%s.mmap.writable' % which, True)
    fixed = self.vars.get('%s.mmap.fixed' % which, True)
    anon = self.vars.get('%s.mmap.anon' % which, True)
    fd_idx = self.vars.get('%s.mmap.fd' % which, 0)
    off = self.vars.get('%s.mmap.off' % which, 0)

    prot = 'PROT_READ'
    if writable: prot += ' | PROT_WRITE'

    va = self.get_va(pid, va_idx)
    if not fixed: va = 0

    if anon:
      flags = 'MAP_PRIVATE | MAP_ANONYMOUS'
    else:
      flags = 'MAP_SHARED'

    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % va
    ccode += '\n  return (intptr_t) mmap(va, 4096, %s, %s, %d, 0x%lxUL);' % \
             (prot, flags, self.get_fd(pid, fd_idx), off)
    return ccode

  def munmap(self, which, pid):
    va_idx = self.vars.get('%s.munmap.va' % which, 0)
    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % self.get_va(pid, va_idx)
    ccode += '\n  return munmap(va, 4096);'
    return ccode

  def mprotect(self, which, pid):
    va_idx = self.vars['%s.mprotect.va' % which]
    writable = self.vars.get('%s.mprotect.writable' % which, False)
    prot = 'PROT_READ'
    if writable:
      prot += ' | PROT_WRITE'
    ccode = ''
    ccode += '\n  int* va = (int*) 0x%lxUL;' % self.get_va(pid, va_idx)
    ccode += '\n  return mprotect(va, 4096, %s);' % prot
    return ccode

  def mem_read(self, which, pid):
    ## TODO: catch SIGSEGV
    va_idx = self.vars['%s.mem_read.va' % which]
    ccode = ''
    ccode += '\n  int* p = (int*) 0x%lxUL;' % self.get_va(pid, va_idx)
    ccode += '\n  return *p;'
    return ccode

  def mem_write(self, which, pid):
    ## TODO: catch SIGSEGV
    va_idx = self.vars['%s.mem_write.va' % which]
    val = self.vars.get('%s.mem_write.databyte' % which, 0)
    ccode = ''
    ccode += '\n  int* p = (int*) 0x%lxUL;' % self.get_va(pid, va_idx)
    ccode += '\n  *p = %d;' % val
    ccode += '\n  return 0;'
    return ccode

def cleanup():
  ccode = ''
  for fn in all_filenames:
    ccode = ccode + '\n  unlink("%s");' % fn
  return ccode

def pretty_print_vars(d):
  r = ''
  for k in sorted(d):
    r = r + '%s: %s\n' % (k, d[k])
  return r

def generate_fs(d):
  print 'Number of test cases:', len(d['Fs'])
  for tidx, t in enumerate(d['Fs']):
    calls = t['calls']
    vars = t['vars']

    fs = FsState(vars)
    for callidx, call in enumerate(calls):
      code = fs.gen_code(call, chr(callidx + ord('a')))
      testcode[tidx][callidx] = code
    setupcode[tidx] = fs.build_dir()

with open(sys.argv[1]) as f:
  d = json.loads(f.read())
  setupcode = {}
  testcode = collections.defaultdict(dict)
  cleanupcode = cleanup()
  gen_ts = d['__gen_ts']
  generate_fs(d)

outprog = open(sys.argv[2], 'w')
outprog.write("""\
#define _GNU_SOURCE 1
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
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
}
""")

for tidx in setupcode:
  outprog.write("""
/*
 * calls: %s
 * vars:  %s
 */""" % (str(d['Fs'][tidx]['calls']),
          pretty_print_vars(d['Fs'][tidx]['vars']).strip().replace('\n', '\n *        ')))

  for phase in ('common', 'proc0', 'proc1', 'final'):
    outprog.write("""
static void setup_%d_%s(void) {%s
}
""" % (tidx, phase, setupcode[tidx][phase]))

  for callidx in testcode[tidx]:
    outprog.write("""
static int test_%d_%d(void) {%s
}
""" % (tidx, callidx, testcode[tidx][callidx]['code']))

outprog.write("""
static void cleanup(void) {%s
}
""" % cleanupcode)

outprog.write("""
struct fstest fstests[] = {""")
for tidx in setupcode:
  outprog.write("""
  { "%s",
    &setup_%d_common, { { &setup_%d_proc0 }, { &setup_%d_proc1 } }, &setup_%d_final,
    { { &test_%d_0, %d, "%s" },
      { &test_%d_1, %d, "%s" } },
    &cleanup },""" \
  % ('fs-%d-%d' % (gen_ts, tidx),
     tidx, tidx, tidx, tidx,
     tidx, testcode[tidx][0]['pid'], d['Fs'][tidx]['calls'][0],
     tidx, testcode[tidx][1]['pid'], d['Fs'][tidx]['calls'][1]))
outprog.write("""
  { 0 }
};
""")
