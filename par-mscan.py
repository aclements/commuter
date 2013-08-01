#!/usr/bin/python

import subprocess, glob, json, os, sys

procs = []
for mtraceout in sorted(glob.glob('mtrace.out.*')):
  mscanout = 'mscan.out.' + mtraceout[len('mtrace.out.'):]
  args = ["../mtrace/mtrace-tools/mscan",
          "--mtrace-log-file=%s" % mtraceout,
          "--check-testcases"] + sys.argv[1:]
  p = subprocess.Popen(args, stdout=file(mscanout, 'w'))
  procs.append((p, args, mscanout))

merged_json = { 'testcases': [] }
for i, (proc, args, mscanout) in enumerate(procs):
  if proc.wait():
    raise subprocess.CalledProcessError(proc.returncode, args)
  d = json.load(file(mscanout))
  merged_json['testcases'].extend(d['testcases'])

print json.dumps(merged_json, indent=2)
