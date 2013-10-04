#!/usr/bin/env python

import subprocess, glob, json, os, sys, argparse

parser = argparse.ArgumentParser(
  epilog='Unknown arguments will be passed to mscan')
parser.add_argument('-d', '--log-dir', metavar='DIR', default='.',
                    help='Read logs from and write output shards to DIR')
args, mscanargs = parser.parse_known_args()

procs = []
for mtraceout in sorted(glob.glob(os.path.join(args.log_dir, 'mtrace.out.*'))):
  mscanout = os.path.join(
    args.log_dir, 'mscan.out.' + mtraceout.rpartition('mtrace.out.')[2])
  cmd = ["../mtrace/mtrace-tools/mscan",
          "--mtrace-log-file=%s" % mtraceout,
          "--check-testcases"] + mscanargs
  p = subprocess.Popen(cmd, stdout=file(mscanout, 'w'))
  procs.append((p, cmd, mscanout))

merged_json = { 'testcases': [] }
for i, (proc, cmd, mscanout) in enumerate(procs):
  if proc.wait():
    raise subprocess.CalledProcessError(proc.returncode, cmd)
  d = json.load(file(mscanout))
  merged_json['testcases'].extend(d['testcases'])

json.dump(merged_json, sys.stdout, indent=2)
