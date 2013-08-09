#!/usr/bin/python

import os, sys, multiprocessing, argparse, re, glob

parser = argparse.ArgumentParser()
parser.add_argument('-d', '--output-dir', metavar='DIR', required=True,
                    help='Store testgen shards in DIR')
parser.add_argument('-j', '--jobs', type=int,
                    default=multiprocessing.cpu_count(),
                    help='Number of shards (and resulting make jobs)')
parser.usage = parser.format_usage().split(':',1)[1].strip() + ' < testgen.c'
args = parser.parse_args()

shard_names = [os.path.join(args.output_dir, 'testgen.%d.c' % i)
               for i in xrange(args.jobs - 1)]
if set(glob.glob(os.path.join(args.output_dir, 'testgen.*.c'))) - \
   set(shard_names):
    parser.error('Output directory is dirty')
outarray = file(os.path.join(args.output_dir, 'testgen.c'), 'w')
outshards = [file(path, 'w') for path in shard_names]

testparts = [p + '\n\n' for p in sys.stdin.read().split('\n\n')]

# Emit common headers
while testparts:
    if 'int test_' in testparts[0]:
        break
    for outshard in outshards:
        outshard.write(testparts[0])
    outarray.write(testparts.pop(0))

# Emit test array
nontest = None
for i, testpart in enumerate(testparts):
    if 'int test_' in testpart:
        assert nontest is None
        for fn in re.findall('^static (.*) {', testpart, flags=re.MULTILINE):
            outarray.write(fn + ';\n')
    elif nontest is None and testpart.strip():
        nontest = i
outarray.write(''.join(testparts[nontest:]))
del testparts[nontest:]

# Divide tests among outshards
shard_size = len(testparts) / len(outshards)
for i, outshard in enumerate(outshards):
    shard = testparts[i * shard_size:(i+1) * shard_size]
    for part in shard:
        outshard.write(re.sub('^static ', '', part, flags=re.MULTILINE))
