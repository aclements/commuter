import spec
import multiprocessing
import re
import copy
import json
import collections

args = spec.parser.parse_args()
callsets = spec.parse_functions(
    args.functions, args.ncomb, __import__(args.module))

def do_callset(i, farg):
    csargs = copy.copy(args)
    suffix = ".%03d" % i
    if csargs.model_file:
        csargs.model_file += suffix
    if csargs.trace_file:
        csargs.trace_file += suffix
    if csargs.test_file:
        csargs.test_file += suffix
    csargs.functions = farg

    spec.main(csargs)

    return csargs

pool = multiprocessing.Pool()
asyncs = []
for i, callset in enumerate(callsets):
    farg = "/".join(c.__name__ for c in callset)
    asyncs.append(pool.apply_async(do_callset, [i, farg]))
pool.close()
subargs = [async.get() for async in asyncs]

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
