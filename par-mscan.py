#!/usr/bin/python

import subprocess, glob, json, os, sys

procs = []
for mtraceout in sorted(glob.glob('mtrace.out.*')):
  args = ["../mtrace/mtrace-tools/mscan",
          "--mtrace-log-file=%s" % mtraceout,
          "--check-testcases"] + sys.argv[1:]
  p = subprocess.Popen(args, stdout=subprocess.PIPE)
  procs.append(p)

merged_json = { 'testcases': [] }
for i, p in enumerate(procs):
  s = p.stdout.read()
  try:
    d = json.loads(s)
  except ValueError, e:
    raise ValueError(str(e) + " from mtrace shard %03d" % i)
  merged_json['testcases'].extend(d['testcases'])
  p.wait()

print json.dumps(merged_json, indent=2)
