#!/usr/bin/python

import subprocess, glob, json, os

procs = []
for mtraceout in sorted(glob.glob('mtrace.out.*')):
  args = ["../mtrace/mtrace-tools/mscan",
          "--mtrace-log-file=%s" % mtraceout,
          "--check-testcases"]
  p = subprocess.Popen(args, stdout=subprocess.PIPE)
  procs.append(p)

merged_json = { 'testcases': [] }
for p in procs:
  s = p.stdout.read()
  d = json.loads(s)
  merged_json['testcases'].extend(d['testcases'])
  p.wait()

print json.dumps(merged_json, indent=2)
