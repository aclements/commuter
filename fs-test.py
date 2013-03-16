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
all_fds = [x for x in range(fd_begin, fd_end)]

def array_lookup_raw(array, idx):
  for k, v in array[:-1]:
    if idx == k: return v
  return array[-1]

class FsState(object):
  def __init__(self, vars):
    self.vars = vars
    self.filenames = SetAllocator(all_filenames)
    self.inodefiles = SetAllocator(['__i%d' % x for x in range(0, 6)])
    self.fds = SetAllocator(all_fds)

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

  def get_fd(self, v):
    return self.fds.get(v)

  def build_dir(self):
    fn_to_ino = {}
    for fn_idx in self.filenames.assigned():
      if not self.array_lookup(('Fs.rootdir', '_valid'), fn_idx, False):
        continue
      ino_idx = self.array_lookup(('Fs.rootdir', '_map'), fn_idx, 0)
      fn_to_ino[self.get_fn(fn_idx)] = self.get_ifn(ino_idx)

    fd_to_ino = {}
    fd_to_off = {}
    for fd_idx in self.fds.assigned():
      if not self.array_lookup(('Fs.fdmap', '_valid'), fd_idx, False):
        continue
      fd_state = self.array_lookup(('Fs.fdmap', '_map'), fd_idx, 0)
      fd_to_ino[self.get_fd(fd_idx)] = self.get_ifn(fd_state['inum'])
      fd_to_off[self.get_fd(fd_idx)] = fd_state['off']

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
        for i in range(0, len):
          ccode += '\n  c = %d;' % array_lookup_raw(inode['data']['_vals'], i)
          ccode += '\n  write(fd, &c, 1);'

      ccode += '\n  close(fd);'

    for fn in fn_to_ino:
      ccode += '\n  link("%s", "%s");' % (fn_to_ino[fn], fn)

    for fd in fd_to_ino:
      ccode += '\n  fd = open("%s", O_RDWR);' % fd_to_ino[fd]
      ccode += '\n  lseek(fd, %d, SEEK_SET);' % fd_to_off[fd]
      ccode += '\n  dup2(fd, %d);' % fd
      ccode += '\n  close(fd);'

    for ino_idx in self.inodefiles.assigned():
      ccode += '\n  unlink("%s");' % self.get_ifn(ino_idx)

    return ccode

  def gen_code(self, m, which):
    f = getattr(self, m)
    return f(which)

  def open(self, which):
    fn_idx = self.vars['Fs.open[%s].pn' % which]
    flags = ['O_RDWR']
    if self.vars.get('Fs.open[%s].excl' % which, True):
      flags.append('O_EXCL')
    if self.vars.get('Fs.open[%s].creat' % which, True):
      flags.append('O_CREAT')
    if self.vars.get('Fs.open[%s].trunc' % which, True):
      flags.append('O_TRUNC')
    if self.vars.get('Fs.open[%s].anyfd' % which, True):
      flags.append('O_ANYFD')
    ccode = ''
    ccode += '\n  return open("%s", %s, 0666);' % (self.get_fn(fn_idx),
                                                   ' | '.join(flags))
    return ccode

  def pread(self, which):
    fd_idx = self.vars['Fs.pread[%s].fd' % which]
    off = self.vars.get('Fs.pread[%s].off' % which, 0)
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = pread(%d, &c, 1, %d);' % (self.get_fd(fd_idx), off)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def pwrite(self, which):
    fd_idx = self.vars['Fs.pwrite[%s].fd' % which]
    off = self.vars.get('Fs.pwrite[%s].off' % which, 0)
    val = self.vars.get('Fs.pwrite[%s].databyte' % which, 0)
    ccode = ''
    ccode += '\n  char c = %d;' % val
    ccode += '\n  ssize_t cc = pwrite(%d, &c, 1, %d);' % (self.get_fd(fd_idx), off)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def read(self, which):
    fd_idx = self.vars['Fs.read[%s].fd' % which]
    ccode = ''
    ccode += '\n  char c;'
    ccode += '\n  ssize_t cc = read(%d, &c, 1);' % self.get_fd(fd_idx)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return c;'
    return ccode

  def write(self, which):
    fd_idx = self.vars['Fs.write[%s].fd' % which]
    val = self.vars.get('Fs.write[%s].databyte' % which, 0)
    ccode = ''
    ccode += '\n  char c = %d;' % val
    ccode += '\n  ssize_t cc = write(%d, &c, 1);' % self.get_fd(fd_idx)
    ccode += '\n  if (cc < 0) return xerrno(cc);'
    ccode += '\n  return cc;'
    return ccode

  def unlink(self, which):
    fn_idx = self.vars['Fs.unlink[%s].pn' % which]
    ccode = ''
    ccode += '\n  return unlink("%s");' % self.get_fn(fn_idx)
    return ccode

  def link(self, which):
    oldfn_idx = self.vars.get('Fs.link[%s].old' % which, 0)
    newfn_idx = self.vars.get('Fs.link[%s].new' % which, 0)
    ccode = ''
    ccode += '\n  return link("%s", "%s");' % (self.get_fn(oldfn_idx),
                                               self.get_fn(newfn_idx))
    return ccode

  def rename(self, which):
    srcfn_idx = self.vars.get('Fs.rename[%s].src' % which, 0)
    dstfn_idx = self.vars.get('Fs.rename[%s].dst' % which, 0)
    ccode = ''
    ccode += '\n  return rename("%s", "%s");' % (self.get_fn(srcfn_idx),
                                                 self.get_fn(dstfn_idx))
    return ccode

  def stat(self, which):
    fn_idx = self.vars['Fs.stat[%s].pn' % which]
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = stat("%s", &st);' % self.get_fn(fn_idx)
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

  def fstat(self, which):
    fd_idx = self.vars['Fs.fstat[%s].fd' % which]
    ccode = ''
    ccode += '\n  struct stat st;'
    ccode += '\n  int r = fstat(%d, &st);' % self.get_fd(fd_idx)
    ccode += '\n  if (r < 0) return xerrno(r);'
    ccode += '\n  /* Hack, to test for approximate equality */'
    ccode += '\n  return st.st_ino ^ st.st_nlink ^ st.st_size;'
    return ccode

def cleanup():
  ccode = ''
  for fn in all_filenames:
    ccode = ccode + '\n  unlink("%s");' % fn
  assert(fd_begin > 3)
  for fd in range(3, fd_end):
    ccode = ccode + '\n  close(%d);' % fd
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
#include "fstest.h"

#ifndef XV6_USER
#define O_ANYFD 0
#endif

static int __attribute__((unused)) xerrno(int r) {
#ifdef XV6_USER
  return r;
#else
  return -errno;
#endif
}
""")

for tidx in setupcode:
  outprog.write("""
/*
 * calls: %s
 * vars:  %s
 */
static void setup_%d(void) {%s
}
""" % (str(d['Fs'][tidx]['calls']),
       pretty_print_vars(d['Fs'][tidx]['vars']).strip().replace('\n', '\n *        '),
       tidx, setupcode[tidx]))

  for callidx in testcode[tidx]:
    outprog.write("""
static int test_%d_%d(void) {%s
}
""" % (tidx, callidx, testcode[tidx][callidx]))

outprog.write("""
static void cleanup(void) {%s
}
""" % cleanupcode)

outprog.write("""
struct fstest fstests[] = {""")
for tidx in setupcode:
  outprog.write("""
  { "%s", &setup_%d, &test_%d_0, &test_%d_1, "%s", "%s", &cleanup },""" \
  % ('fs-%d-%d' % (gen_ts, tidx),
     tidx, tidx, tidx,
     d['Fs'][tidx]['calls'][0],
     d['Fs'][tidx]['calls'][1]))
outprog.write("""
  { 0, 0, 0 }
};
""")
