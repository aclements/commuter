#!/usr/bin/python

import os, multiprocessing, subprocess, argparse

parser = argparse.ArgumentParser()
parser.add_argument('-d', '--log-dir', metavar='DIR', default='.',
                    help='Store output logs in DIR')
parser.add_argument('-j', '--jobs', type=int,
                    default=multiprocessing.cpu_count(),
                    help='Number of parallel jobs')
args = parser.parse_args()

os.system("make HW=mtrace")

null = open('/dev/null', 'rw')
procs = []
for n in range(0, args.jobs):
  cmd = ["make",
         "HW=mtrace",
         "MTRACEOUT=" + os.path.join(args.log_dir, "mtrace.out.%03d" % n),
         "RUN=fstest -t -n %d -p %d; halt" % (args.jobs, n),
         "QEMUNOREDIR=x",
         "QEMUOUTPUT=" + os.path.join(args.log_dir, "qemu.out.%03d" % n),
         os.path.join(args.log_dir, "mtrace.out.%03d-scripted" % n)]
  p = subprocess.Popen(cmd, stdout=null, stdin=null)
  procs.append(p)

for p in procs:
  p.wait()

