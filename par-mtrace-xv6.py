#!/usr/bin/python

import os, multiprocessing, subprocess

ncpu = multiprocessing.cpu_count()

os.system("make HW=mtrace mscan.kern")

procs = []
for n in range(0, ncpu):
  out = open('qemu.out.%d' % n, 'w')
  args = ["make", "HW=mtrace",
                  "MTRACEOUT=mtrace.out.%d" % n,
                  "RUN=fstest -t -n %d -p %d; halt" % (ncpu, n),
                  "QEMUNOREDIR=x",
                  "mtrace.out.%d-scripted" % n]
  p = subprocess.Popen(args, stdout=out, stderr=subprocess.STDOUT)
  procs.append(p)

for p in procs:
  p.wait()

