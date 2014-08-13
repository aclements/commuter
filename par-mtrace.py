#!/usr/bin/env python

import sys, os, multiprocessing, subprocess, argparse, tempfile

parser = argparse.ArgumentParser()
parser.add_argument('-m', '--mode', required=True, choices=['xv6','linux'],
                    help='OS to run under mtrace')
parser.add_argument('-k', '--kernel',
                    help='Kernel image (default depends on --mode)')
parser.add_argument('--fs-type', default='ramfs',
                    help='Run fstest on a file system of this type '
                    '(default: %(default)s)')
parser.add_argument('-d', '--log-dir', metavar='DIR', default='.',
                    help='Store output logs in DIR')
parser.add_argument('-j', '--jobs', type=int,
                    default=multiprocessing.cpu_count(),
                    help='Number of parallel jobs')
args = parser.parse_args()

if args.kernel == None and args.mode == 'linux':
  args.kernel = '../linux-mtrace/arch/x86_64/boot/bzImage'
if args.kernel != None and not os.path.isfile(args.kernel):
  parser.error('kernel file not found: %s' % args.kernel)
if args.mode != 'linux' and args.fs_type != 'ramfs':
  parser.error('mode %s only supports ramfs' % args.mode)

if args.mode == 'xv6':
  hw = 'mtrace'
elif args.mode == 'linux':
  hw = 'linuxmtrace'

run = qemuextra = ''

if args.fs_type != 'ramfs':
  # Build file system image
  print >>sys.stderr, 'Creating %s disk image...' % args.fs_type
  fsimg = tempfile.NamedTemporaryFile()
  # Default ramdisk size is 4MB
  fsimg.write('\0' * (4 * 1024 * 1024))
  fsimg.flush()
  fsargs = []
  if args.fs_type.startswith('ext'):
    fsargs.append('-F')           # Don't prompt for regular file
  elif args.fs_type == 'btrfs':
    fsargs.append('-f')           # Don't prompt for regular file
  subprocess.check_call(
    ['/sbin/mkfs', '-t', args.fs_type] + fsargs + [fsimg.name])
  # When VM boots, copy image to ramdisk and mount it
  run = ('dd if=/dev/sda of=/dev/ram0 && '
         'mkdir ram0 && mount /dev/ram0 ram0 && cd ram0 && ' + run)
  qemuextra += ' -hda %s' % fsimg.name

print >>sys.stderr, 'Building for HW=%s...' % hw
os.system("make HW=%s" % hw)

print >>sys.stderr, 'Running...'
null = open('/dev/null', 'r+')
procs = []
for n in range(0, args.jobs):
  qemuoutput = os.path.join(args.log_dir, "qemu.out.%03d" % n)
  cmd = ["make",
         "HW=%s" % hw,
         "MTRACEOUT=" + os.path.join(args.log_dir, "mtrace.out.%03d" % n),
         "RUN=%s /fstest -t -n %d -p %d; /halt" % (run, args.jobs, n),
         "QEMUNOREDIR=x",
         "QEMUOUTPUT=" + qemuoutput,
         os.path.join(args.log_dir, "mtrace.out.%03d-scripted" % n)]
  if args.kernel:
    cmd.append('KERN=%s' % args.kernel)
  if qemuextra:
    cmd.append('QEMUEXTRA=%s' % qemuextra)
  p = subprocess.Popen(cmd, stdout=null, stdin=null)
  procs.append((p, qemuoutput))

for i, (p, qemuoutput) in enumerate(procs):
  p.wait()
  qemulog = open(qemuoutput, 'U').read()
  if 'fstest: done\n' not in qemulog:
    print >>sys.stderr, 'Warning: fstest shard %d failed; see %s' % \
      (i, qemuoutput)
