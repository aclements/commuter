import json
import sys
import os
import struct
import errno
import itertools
import collections

filenames = [str(x) for x in range(0, 15)]

def getdir(vars):
  files = set()
  if vars['Fs.dir._valid'][-1]:
    files.update(filenames)
  for fnidx, exists in vars['Fs.dir._valid'][:-1]:
    if not exists:
      if filenames[fnidx] in files: files.remove(filenames[fnidx])
    else:
      files.add(filenames[fnidx])

  fnidx_to_ino = vars.get('Fs.dir._map', [0])
  dir = {}
  for fn in files:
    ino = fnidx_to_ino[-1]
    for fnidx2, ino2 in fnidx_to_ino[:-1]:
      if fn == filenames[fnidx2]:
        ino = ino2
    dir[fn] = ino

  ino_to_data = vars.get('Fs.idata._map', [0])
  idata = {}
  for ino in set(dir.values()):
    data = ino_to_data[-1]
    for ino2, data2 in ino_to_data[:-1]:
      if ino == ino2:
        data = data2
    idata[ino] = data

  return dir, idata

def build_dir(dir, idata):
  ccode = ''
  for ino in set(dir.values()):
    ifn = '__i%d' % ino
    ccode = ccode + """
  {
    int fd = open("%s", O_CREAT | O_EXCL | O_RDWR, 0666);
    char c = %d;
    write(fd, &c, 1);
    close(fd);
  }""" % (ifn, idata[ino])

  for fn, ino in dir.iteritems():
    ifn = '__i%d' % ino
    ccode = ccode + """\n  link("%s", "%s");""" % (ifn, fn)

  for ino in set(dir.values()):
    ifn = '__i%d' % ino
    ccode = ccode + """\n  unlink("%s");""" % ifn

  return ccode

def cleanup():
  ccode = ''
  for fn in filenames:
    ccode = ccode + """\n  unlink("%s");""" % fn
  return ccode

class FsRunner:
  @classmethod
  def run_method(cls, m, which, vars):
    f = getattr(cls, m)
    return f(which, vars)

  @staticmethod
  def open(which, vars):
    fnidx = vars['Fs.open[%s].fn' % which]
    flags = ['O_RDWR']
    if vars.get('Fs.open[%s].excl' % which, True):
      flags.append('O_EXCL')
    if vars.get('Fs.open[%s].creat' % which, True):
      flags.append('O_CREAT')
    if vars.get('Fs.open[%s].trunc' % which, True):
      flags.append('O_TRUNC')
    return """
  {
    int fd = open("%s", %s | O_ANYFD, 0666);
    /* XXX O_ANYFD because model has no notion of lowest-FD yet */
    if (fd < 0)
      return xerrno(fd);
    close(fd);
    return 0;
  }""" % (filenames[fnidx], ' | '.join(flags))

  @staticmethod
  def read(which, vars):
    fnidx = vars['Fs.read[%s].fn' % which]
    return """
  {
    int fd = open("%s", O_RDONLY | O_ANYFD);
    if (fd < 0)
      return xerrno(fd);
    char c;
    ssize_t cc = read(fd, &c, 1);
    close(fd);
    return (cc > 0) ? c : INT_MIN;
  }""" % filenames[fnidx]

  @staticmethod
  def write(which, vars):
    fnidx = vars['Fs.write[%s].fn' % which]
    d = vars.get('Fs.write[%s].data' % which, 0)
    return """
  {
    int fd = open("%s", O_WRONLY | O_TRUNC | O_ANYFD);
    if (fd < 0)
      return xerrno(fd);
    char c = %d;
    ssize_t cc = write(fd, &c, 1);
    close(fd);
    return cc;
  }""" % (filenames[fnidx], d)

  @staticmethod
  def unlink(which, vars):
    fnidx = vars['Fs.unlink[%s].fn' % which]
    return """\n  return unlink("%s");""" % filenames[fnidx]

  @staticmethod
  def link(which, vars):
    oldfnidx = vars.get('Fs.link[%s].oldfn' % which, 0)
    newfnidx = vars.get('Fs.link[%s].newfn' % which, 0)
    return """\n  return link("%s", "%s");""" % \
           (filenames[oldfnidx], filenames[newfnidx])

  @staticmethod
  def rename(which, vars):
    srcfnidx = vars.get('Fs.rename[%s].src' % which, 0)
    dstfnidx = vars.get('Fs.rename[%s].dst' % which, 0)
    return """\n return rename("%s", "%s");""" % \
           (filenames[srcfnidx], filenames[dstfnidx])

  @staticmethod
  def stat(which, vars):
    fnidx = vars['Fs.stat[%s].fn' % which]
    return """
  {
    struct stat st;
    int r = stat("%s", &st);
    if (r < 0)
      return xerrno(r);
    /* Hack, to test for approximate equality */
    return st.st_ino ^ st.st_nlink ^ st.st_size;
  }""" % (filenames[fnidx])

def run_calls(idxcalls, vars):
  r = range(0, len(idxcalls))
  for idx, c in idxcalls:
    r[idx] = FsRunner.run_method(c, chr(idx + ord('a')), vars)
  return r

def pretty_print_vars(d):
  r = ''
  for k in sorted(d):
    r = r + '%s: %s\n' % (k, d[k])
  return r

with open(sys.argv[1]) as f:
  d = json.loads(f.read())

outprog = open(sys.argv[2], 'w')

setupcode = {}
testcode = collections.defaultdict(dict)
cleanupcode = cleanup()

print 'Number of test cases:', len(d['Fs'])
for tidx, t in enumerate(d['Fs']):
  calls = t['calls']
  vars = t['vars']

  dir, idata = getdir(vars)
  setupcode[tidx] = build_dir(dir, idata)
  for callidx, call in enumerate(calls):
    code = FsRunner.run_method(call, chr(callidx + ord('a')), vars)
    testcode[tidx][callidx] = code

outprog.write("""\
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

static int xerrno(int r) {
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
  { &setup_%d, &test_%d_0, &test_%d_1, "%s", "%s", &cleanup },""" \
  % (tidx, tidx, tidx,
     d['Fs'][tidx]['calls'][0],
     d['Fs'][tidx]['calls'][1]))
outprog.write("""
  { 0, 0, 0 }
};
""")
