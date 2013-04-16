#!/usr/bin/python

import subprocess, glob, json, os

procs = []
for mtraceout in glob.glob('mtrace.out.*'):
  args = ["%s/proj/mtrace/mtrace-tools/mscan" % os.environ['HOME'],
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
