import json
import collections

with open('mtrace.json') as f:
  mtrace = json.load(f)

testcases = []
thistest = None

for e in mtrace:
  if thistest is not None:
    thistest.append(e)
  if e['type'] == 'host' and e['host_type'] == 'access_all_cpu':
    if e['mode'] == 'ascope':
      thistest = [e]
    if e['mode'] == 'disable':
      testcases.append(thistest)
      thistest = None

for t in testcases:
  print 'testcase', t[0]['access_str']
  scopecount = collections.defaultdict(int)
  cpureads = collections.defaultdict(set)
  cpuwrites = collections.defaultdict(set)
  for e in t:
    cpu = e['cpu']
    if e['type'] == 'ascope' and e['name'].startswith('syscall:'):
      if e['exit'] == 0:
        scopecount[cpu] = scopecount[cpu] + 1
      else:
        scopecount[cpu] = scopecount[cpu] - 1
    if e['type'] == 'access' and scopecount[cpu] > 0:
      ## XXX actually use [host_addr, host_addr + bytes), and
      ## keep track of pc + guest_addr for each byte access.
      if e['acctype'] == 'st':
        cpuwrites[cpu].add(e['guest_addr'])
      cpureads[cpu].add(e['guest_addr'])

  for c in cpureads:
    # print 'cpu', c, 'nr', len(cpureads[cpu]), 'nw', len(cpuwrites[cpu])
    pass

  write_disjoint = cpuwrites[0].isdisjoint(cpuwrites[1])
  rw_disjoint = cpureads[0].isdisjoint(cpuwrites[1]) and \
                cpureads[1].isdisjoint(cpuwrites[0])
  print 'disjoint', write_disjoint, rw_disjoint
