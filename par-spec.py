#!/usr/bin/env python

import spec
import multiprocessing
import re
import copy
import json
import collections
import traceback
import sys

def wrapped_main(*args):
    # Blarg!  multiprocessing eats tracebacks
    try:
        return spec.main(*args)
    except Exception as e:
        tb = traceback.format_exc()
        print >>sys.stderr, "Exception in child:\n" + tb
        if len(e.args) == 1:
            e.args = ("%s\nin child at:\n" + tb,)
        raise

args = spec.parser.parse_args()
callsets = spec.parse_functions(
    args.functions, args.ncomb, __import__(args.module))
pool = multiprocessing.Pool()
subargs = []
asyncs = []
for i, callset in enumerate(callsets):
    csargs = copy.copy(args)
    suffix = ".%03d" % i
    if csargs.model_file:
        csargs.model_file += suffix
    if csargs.trace_file:
        csargs.trace_file += suffix
    if csargs.test_file:
        csargs.test_file += suffix
    csargs.functions = "/".join(callset)
    asyncs.append(pool.apply_async(wrapped_main, [csargs]))
    subargs.append(csargs)
pool.close()
for async in asyncs:
    # This is the only way to propagate exceptions up
    async.get()
pool.join()

print "Model execution complete"

def merge_model_files(ins, out):
    data = {"tests": collections.OrderedDict()}
    for inpath in ins:
        d = json.load(file(inpath), object_pairs_hook=collections.OrderedDict)
        data["tests"].update(d["tests"])
    json.dump(data, file(out, "w"), indent=2)

def merge_trace_files(ins, out):
    outf = file(out, "w")
    for inpath in ins:
        outf.write(file(inpath).read())

def merge_test_files(ins, out):
    merged = None
    for inpath in ins:
        data = file(inpath).read()
        parts = re.split(r"(^//\+\+\+ .*\n?)", data, flags=re.MULTILINE)
        if parts[0] != "":
            raise ValueError("Test file %s does not begin with //+++" % inpath)
        parts.pop(0)
        pairs = zip(parts[::2], parts[1::2])
        if merged is None:
            merged = pairs
        else:
            if [m[0] for m in merged] != [p[0] for p in pairs]:
                raise ValueError(
                    "Test file %s parts do not match template" % inpath)
            for i in range(len(merged)):
                kind = merged[i][0].split()[1]
                if kind == "common":
                    if merged[i][1] != pairs[i][1]:
                        raise ValueError(
                            "Test file %s part %d does not match template" %
                            (inpath, i))
                elif kind == "tests":
                    merged[i] = (merged[i][0], merged[i][1] + pairs[i][1])
                else:
                    raise ValueError("Bad part kind %r in %s" % (kind, inpath))

    file(out, "w").write("".join(m[1] for m in merged))

if args.model_file:
    print "Merging model files..."
    merge_model_files([subarg.model_file for subarg in subargs], args.model_file)

if args.trace_file:
    print "Merging trace files..."
    merge_trace_files([subarg.trace_file for subarg in subargs], args.trace_file)

if args.test_file:
    print "Merging test files..."
    merge_test_files([subarg.test_file for subarg in subargs], args.test_file)
