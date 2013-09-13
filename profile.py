#!/usr/bin/python

import sys
import argparse
import json
import collections

FIELDS = ['ntests', 'npaths', 'ncomm', 'nerr', 'max_paths', 'max_path_tests']
ADDITIVE = ['ntests', 'npaths', 'ncomm', 'nerr',
            'diffntests', 'diffnpaths', 'diffncomm']
SPECS = {'pct': '{:.2f}%', 'diff': '{:+}'}

class Sample(object):
    def __init__(self, callset):
        self.callset = callset
        self.npaths = 0
        self.ncomm = 0
        self.ntests = 0
        self.nerr = 0
        self.test_hist = collections.Counter()

    @property
    def max_paths(self):
        return self.test_hist[self.max_path_tests]

    @property
    def max_path_tests(self):
        return max(self.test_hist.keys())

def process(fp):
    model = json.load(fp)
    res = {}
    for callset, paths in model['tests'].iteritems():
        sample = Sample(callset)
        res[callset] = sample

        for pathinfo in paths.itervalues():
            if pathinfo.get('exception'):
                sample.nerr += 1
                continue
            sample.npaths += 1
            if pathinfo['diverge'] == '':
                sample.ncomm += 1
            if 'tests' in pathinfo:
                ntests = len(pathinfo['tests'])
            else:
                ntests = 0
            sample.ntests += ntests
            sample.test_hist[ntests] += 1

    return res

class Delta(object):
    def __init__(self, callset, a, b, field):
        self.callset = callset
        aval, bval = getattr(a, field), getattr(b, field)
        self.pct = 100 * float(bval - aval) / aval
        for field in FIELDS:
            setattr(self, "diff" + field,
                    getattr(b, field) - getattr(a, field))

def diff(samples1, samples2, field):
    res = {}
    for callset, sample1 in samples1.iteritems():
        sample2 = samples2[callset]
        res[callset] = Delta(callset, sample1, sample2, field)
    return res

def main(argv):
    parser = argparse.ArgumentParser(description='Profile models')
    parser.add_argument('--field', choices=FIELDS, default='ntests',
                        help='Field to sort and compare by')
    parser.add_argument('model', type=file,
                        help='The model.out to profile')
    parser.add_argument('model2', type=file, nargs='?',
                        help='The model.out to compare against')
    args = parser.parse_args(argv)

    samples = process(args.model)
    if args.model2:
        samples2 = process(args.model2)
        out = diff(samples, samples2, args.field).values()
        fields = ['pct', 'diff' + args.field, 'callset'] + \
                 ['diff' + f for f in FIELDS if f != args.field]
        sortby = 'pct'
    else:
        out = samples.values()
        fields = [args.field, 'callset'] + \
                 [f for f in FIELDS if f != args.field]
        sortby = args.field

    # Format table
    table = [[f.replace('diff', u'\u0394') for f in fields]]
    sums = [0 if field in ADDITIVE else
            'TOTAL' if field == 'callset' else ''
            for field in fields]
    for obj in sorted(out, key=lambda s: getattr(s, sortby), reverse=True):
        table.append([SPECS.get(f, '{}').format(getattr(obj, f))
                      for f in fields])
        for i, field in enumerate(fields):
            if field in ADDITIVE:
                sums[i] += getattr(obj, field)
    table.append(map(str, sums))

    # Print table
    widths = [max(map(len, col)) * (1 if field == 'callset' else -1)
              for field, col in zip(fields, zip(*table))]
    for row in table:
        print ' '.join(v.ljust(w).rjust(-w)
                       for v, w in zip(row, widths)).encode('utf8')

if __name__ == "__main__":
    main(sys.argv[1:])
