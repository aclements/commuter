import json
import sys
import os
import struct

filenames = ['0', '1', '2', '3', '4', '5']

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

def clean_dir(dir):
  for fn, _ in dir.iteritems():
    os.unlink(fn)

with open(sys.argv[1]) as f:
  d = json.loads(f.read())

for t in d['Fs']:
  calls = t['calls']
  vars = t['vars']

  dir, idata = getdir(vars)
  build_dir(dir, idata)
  clean_dir(dir)
