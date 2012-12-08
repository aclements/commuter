import json
import sys
import os
import struct
import errno
import itertools

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
  for ino in set(dir.values()):
    fd = os.open('__i%d' % ino, os.O_CREAT | os.O_EXCL | os.O_RDWR)
    os.write(fd, struct.pack('b', idata[ino]))
    os.close(fd)
  for fn, ino in dir.iteritems():
    os.link('__i%d' % ino, fn)
  for ino in set(dir.values()):
    os.unlink('__i%d' % ino)

def cleanup():
  for fn in filenames:
    try:
      os.unlink(fn)
    except OSError, err:
      if err.errno != errno.ENOENT:
        raise

class FsRunner:
  @classmethod
  def run_method(cls, m, which, vars):
    f = getattr(cls, m)
    try:
      return f(which, vars)
    except OSError, err:
      return ('err', err.errno)

  @staticmethod
  def open(which, vars):
    fnidx = vars['Fs.open[%s].fn' % which]
    flags = os.O_RDWR
    if vars.get('Fs.open[%s].excl' % which, True):
      flags = flags | os.O_EXCL
    if vars.get('Fs.open[%s].creat' % which, True):
      flags = flags | os.O_CREAT
    if vars.get('Fs.open[%s].trunc' % which, True):
      flags = flags | os.O_TRUNC
    os.close(os.open(filenames[fnidx], flags))

  @staticmethod
  def read(which, vars):
    fnidx = vars['Fs.read[%s].fn' % which]
    fd = os.open(filenames[fnidx], os.O_RDONLY)
    d = os.read(fd, 4096)
    os.close(fd)
    return d

  @staticmethod
  def write(which, vars):
    fnidx = vars['Fs.write[%s].fn' % which]
    d = vars.get('Fs.write[%s].data' % which, 0)
    fd = os.open(filenames[fnidx], os.O_WRONLY | os.O_TRUNC)
    os.write(fd, struct.pack('b', d))
    os.close(fd)

  @staticmethod
  def unlink(which, vars):
    fnidx = vars['Fs.unlink[%s].fn' % which]
    os.unlink(filenames[fnidx])

  @staticmethod
  def link(which, vars):
    oldfnidx = vars.get('Fs.link[%s].oldfn' % which, 0)
    newfnidx = vars.get('Fs.link[%s].newfn' % which, 0)
    os.link(filenames[oldfnidx], filenames[newfnidx])

  @staticmethod
  def rename(which, vars):
    srcfnidx = vars.get('Fs.rename[%s].src' % which, 0)
    dstfnidx = vars.get('Fs.rename[%s].dst' % which, 0)
    os.rename(filenames[srcfnidx], filenames[dstfnidx])

def run_calls(idxcalls, vars):
  r = {}
  for idx, c in idxcalls:
    r[idx] = FsRunner.run_method(c, chr(idx + ord('a')), vars)
  return r

with open(sys.argv[1]) as f:
  d = json.loads(f.read())

for t in d['Fs']:
  calls = t['calls']
  vars = t['vars']

  dir, idata = getdir(vars)
  enumcalls = enumerate(calls)
  rvs = []
  for ec in itertools.permutations(enumcalls):
    build_dir(dir, idata)
    rvs.append(run_calls(ec, vars))
    cleanup()

  if any([r != rvs[0] for r in rvs]):
    print 'non-commutative:', calls
    print rvs
    print 'vars:', vars

