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
  if vars['Fs.dir.valid'][-1]:
    files.update(filenames)
  for fnidx, exists in vars['Fs.dir.valid'][:-1]:
    if not exists:
      if filenames[fnidx] in files: files.remove(filenames[fnidx])
    else:
      files.add(filenames[fnidx])

  fnidx_to_ino = vars.get('Fs.dir', [0])
  dir = {}
  for fn in files:
    ino = fnidx_to_ino[-1]
    for fnidx2, ino2 in fnidx_to_ino[:-1]:
      if fn == filenames[fnidx2]:
        ino = ino2
    dir[fn] = ino

  ino_to_data = vars.get('Fs.idata', [0])
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
    fd = os.open(ifn, os.O_CREAT | os.O_EXCL | os.O_RDWR)
    os.write(fd, struct.pack('b', idata[ino]))
    os.close(fd)

    ccode = ccode + """
      {
        int fd = open("%s", O_CREAT | O_EXCL | O_RDWR, 0666);
        char c = %d;
        write(fd, &c, 1);
        close(fd);
      }
      """ % (ifn, idata[ino])
  for fn, ino in dir.iteritems():
    ifn = '__i%d' % ino
    os.link(ifn, fn)
    ccode = ccode + """
      link("%s", "%s");
      """ % (ifn, fn)
  for ino in set(dir.values()):
    ifn = '__i%d' % ino
    os.unlink(ifn)
    ccode = ccode + """
      unlink("%s");
      """ % ifn
  return ccode

def cleanup():
  ccode = ''
  for fn in filenames:
    try:
      os.unlink(fn)
    except OSError, err:
      if err.errno != errno.ENOENT:
        raise
    ccode = ccode + """
      unlink("%s");
      """ % fn
  return ccode

class FsRunner:
  @classmethod
  def run_method(cls, m, which, vars):
    f = getattr(cls, m)
    ccode = ['']
    try:
      rv = f(which, vars, ccode)
      return (rv, ccode[0])
    except OSError, err:
      return (('err', err.errno), ccode[0])

  @staticmethod
  def open(which, vars, cc):
    fnidx = vars['Fs.open[%s].fn' % which]
    flags = os.O_RDWR
    if vars.get('Fs.open[%s].excl' % which, True):
      flags = flags | os.O_EXCL
    if vars.get('Fs.open[%s].creat' % which, True):
      flags = flags | os.O_CREAT
    if vars.get('Fs.open[%s].trunc' % which, True):
      flags = flags | os.O_TRUNC
    cc[0] = cc[0] + """
      {
        int fd = open("%s", 0x%x, 0666);
        if (fd < 0)
          return -errno;
        close(fd);
        return 0;
      }
      """ % (filenames[fnidx], flags)
    os.close(os.open(filenames[fnidx], flags))

  @staticmethod
  def read(which, vars, cc):
    fnidx = vars['Fs.read[%s].fn' % which]
    cc[0] = cc[0] + """
      {
        int fd = open("%s", O_RDONLY);
        if (fd < 0)
          return -errno;
        char c;
        ssize_t cc = read(fd, &c, 1);
        close(fd);
        return (cc > 0) ? c : INT_MIN;
      }
      """ % filenames[fnidx]
    fd = os.open(filenames[fnidx], os.O_RDONLY)
    d = os.read(fd, 4096)
    os.close(fd)
    return d

  @staticmethod
  def write(which, vars, cc):
    fnidx = vars['Fs.write[%s].fn' % which]
    d = vars.get('Fs.write[%s].data' % which, 0)
    cc[0] = cc[0] + """
      {
        int fd = open("%s", O_WRONLY | O_TRUNC);
        if (fd < 0)
          return -errno;
        char c = %d;
        ssize_t cc = write(fd, &c, 1);
        close(fd);
        return cc;
      }
      """ % (filenames[fnidx], d)
    fd = os.open(filenames[fnidx], os.O_WRONLY | os.O_TRUNC)
    os.write(fd, struct.pack('b', d))
    os.close(fd)

  @staticmethod
  def unlink(which, vars, cc):
    fnidx = vars['Fs.unlink[%s].fn' % which]
    cc[0] = cc[0] + """
      return unlink("%s");
      """ % filenames[fnidx]
    os.unlink(filenames[fnidx])

  @staticmethod
  def link(which, vars, cc):
    oldfnidx = vars.get('Fs.link[%s].oldfn' % which, 0)
    newfnidx = vars.get('Fs.link[%s].newfn' % which, 0)
    cc[0] = cc[0] + """
      return link("%s", "%s");
      """ % (filenames[oldfnidx], filenames[newfnidx])
    os.link(filenames[oldfnidx], filenames[newfnidx])

  @staticmethod
  def rename(which, vars, cc):
    srcfnidx = vars.get('Fs.rename[%s].src' % which, 0)
    dstfnidx = vars.get('Fs.rename[%s].dst' % which, 0)
    cc[0] = cc[0] + """
      return rename("%s", "%s");
      """ % (filenames[srcfnidx], filenames[dstfnidx])
    os.rename(filenames[srcfnidx], filenames[dstfnidx])

def run_calls(idxcalls, vars):
  r = range(0, len(idxcalls))
  for idx, c in idxcalls:
    r[idx] = FsRunner.run_method(c, chr(idx + ord('a')), vars)
  return r

with open(sys.argv[1]) as f:
  d = json.loads(f.read())

outprog = open(sys.argv[2], 'w')

setupcode = {}
testcode = collections.defaultdict(dict)
cleanupcode = ''
tidxcalls = []

for tidx, t in enumerate(d['Fs']):
  calls = t['calls']
  vars = t['vars']
  tidxcalls.append(calls)

  dir, idata = getdir(vars)
  enumcalls = enumerate(calls)
  rvs = []
  for ec in itertools.permutations(enumcalls):
    setupcode[tidx] = build_dir(dir, idata)
    rv = run_calls(ec, vars)
    rvs.append([x[0] for x in rv])
    for idx, call in ec:
      testcode[tidx][idx] = rv[idx][1]
    cleanupcode = cleanup()

  if any([r != rvs[0] for r in rvs]):
    print 'non-commutative:', calls
    print rvs
    print 'vars:', vars

outprog.write("""
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <unistd.h>
#include "fstest.h"
""")

for tidx in setupcode:
  outprog.write("""
    static void setup_%d(void) {
      %s
    }
    """ % (tidx, setupcode[tidx]))

  for callidx in testcode[tidx]:
    outprog.write("""
      static int test_%d_%d(void) {
        %s
      }
      """ % (tidx, callidx, testcode[tidx][callidx]))

outprog.write("""
  static void cleanup(void) {
    %s
  }
  """ % cleanupcode)

outprog.write("""
  struct fstest fstests[] = {
  """)
for tidx in setupcode:
  outprog.write("""
    { &setup_%d, &test_%d_0, &test_%d_1, "%s", "%s", &cleanup },
    """ % (tidx, tidx, tidx, tidxcalls[tidx][0], tidxcalls[tidx][1]))
outprog.write("""
    { 0, 0, 0 }
  };
  """)

