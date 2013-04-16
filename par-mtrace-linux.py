#!/usr/bin/python

import os, multiprocessing, subprocess, signal

ncpu = multiprocessing.cpu_count()

nfsd = subprocess.Popen(["./nfs-server.sh", "/tmp/nfs-export"])

null = open('/dev/null', 'rw')
procs = []
disks = []
for n in range(0, ncpu):
  disk = '/mnt/tmpfs/cow-%d.img' % n
  subprocess.call(['qemu-img', 'create',
                   '-f', 'qcow2',
                   '-b', '%s/fs.img' % os.getcwd(),
                   disk])
  disks.append(disk)

  args = ["./mtrace-scripted.sh",
          "mtrace.out.%d" % n,
          disk,
          "qemu.out.%d" % n,
          "fstest_parts=%d" % ncpu,
          "fstest_thispart=%d" % n]
  p = subprocess.Popen(args, stdout=null, stdin=null, stderr=null)
  procs.append(p)

for p in procs:
  p.wait()

for d in disks:
  os.unlink(d)

os.kill(nfsd.pid, signal.SIGTERM)
nfsd.wait()

