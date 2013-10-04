#!/usr/bin/env python

import os, multiprocessing, subprocess, argparse

parser = argparse.ArgumentParser()
parser.add_argument('-m', '--mode', required=True, choices=['xv6','linux'],
                    help='OS to run under mtrace')
parser.add_argument('-k', '--kernel',
                    help='Kernel image (default depends on --mode)')
parser.add_argument('-d', '--log-dir', metavar='DIR', default='.',
                    help='Store output logs in DIR')
parser.add_argument('-j', '--jobs', type=int,
                    default=multiprocessing.cpu_count(),
                    help='Number of parallel jobs')
args = parser.parse_args()

if args.kernel == None and args.mode == 'linux':
  args.kernel = '../pk/arch/x86_64/boot/bzImage'
if args.kernel != None and not os.path.isfile(args.kernel):
  parser.error('kernel file not found: %s' % args.kernel)

if args.mode == 'xv6':
  hw = 'mtrace'
elif args.mode == 'linux':
  hw = 'linuxmtrace'

os.system("make HW=%s" % hw)

null = open('/dev/null', 'r+')
procs = []
for n in range(0, args.jobs):
  cmd = ["make",
         "HW=%s" % hw,
         "MTRACEOUT=" + os.path.join(args.log_dir, "mtrace.out.%03d" % n),
         "RUN=fstest -t -n %d -p %d; halt" % (args.jobs, n),
         "QEMUNOREDIR=x",
         "QEMUOUTPUT=" + os.path.join(args.log_dir, "qemu.out.%03d" % n),
         os.path.join(args.log_dir, "mtrace.out.%03d-scripted" % n)]
  if args.kernel:
    cmd.append('KERN=%s' % args.kernel)
  p = subprocess.Popen(cmd, stdout=null, stdin=null)
  procs.append(p)

for p in procs:
  p.wait()

