import simsym
import z3
import z3printer
import collections
import itertools
import sys
import argparse
import os
import z3util
import pprint
import json
import progress
import testgen

# A test module must have the following two attributes:
#
# * model_class must be the state class whose methods are the
#   operations to test.  The test operations must be decorated with
#   @model.methodwrap.
#
# * model_testgen (optional) must be the test generator class for this
#   model.  It should subclass and implement testgen.TestGenerator.
#   If this attribute is not present, tests cannot be generated.

TestResult = collections.namedtuple(
    'TestResult', 'diverge results post_states op_states')

def test(base, *calls):
    # XXX This codifies "regular" commutativity, not strong
    # commutativity.  They're equivalent for pairs, which is all we
    # use in the paper, but we should fix this.

    init = base.var(base.__name__)

    callnames = [chr(idx + ord('a')) for idx in range(len(calls))]

    # Create arguments for each call.  We reuse these arguments in
    # each permutation, so each call receives the same arguments each
    # time we test it.
    args = []
    for callname, call in zip(callnames, calls):
        arg_name = '%s.%s' % (callname, call.__name__)
        args.append(call.arg_struct_type.var(arg_name))

    all_s = []
    all_r = []
    # post_states[perm_index][step_index + 1] is the state after step
    # step_index in permutation perm_index.
    post_states = []
    # op_states[op_index][perm_index] is a pair of the states before
    # and after operation op_index in permutation perm_index.
    op_states = [[] for _ in calls]

    for callseq in itertools.permutations(range(0, len(calls))):
        prestate = init
        post_states.append([prestate])
        s = init.copy()
        r = [None] * len(callseq)
        seqname = ''.join(map(lambda i: callnames[i], callseq))
        for idx in callseq:
            # Include the sequence and call name in all anonymous
            # variable names
            simsym.anon_info = '_seq' + seqname + '_call' + callnames[idx]
            # Build the Python arguments dictionary and copy each
            # argument, just in case the call mutates it
            arg_struct = args[idx]
            cargs = {arg: getattr(arg_struct, arg).copy()
                     for arg in arg_struct._fields}
            # Invoke the call
            r[idx] = calls[idx](s, **cargs)
            snapshot = s.copy()
            post_states[-1].append(snapshot)
            op_states[idx].append((prestate, snapshot))
            prestate = snapshot
            # Clean up
            simsym.anon_info = ''
        all_s.append(s)
        all_r.append(r)

    diverge = ()
    if simsym.symor([all_r[0] != r for r in all_r[1:]]):
        diverge += ('results',)
    if simsym.symor([all_s[0] != s for s in all_s[1:]]):
        diverge += ('state',)

    return TestResult(diverge, all_r, post_states, op_states)

def expr_vars(e):
    """Return an AstSet of uninterpreted constants in e.

    Uninterpreted constants are what people normally think of as
    "variables".  This is in contrast with interpreted constants such
    as the number 2.  Note that this will also return values that
    belong to universes of uninterpreted sorts, since there is no
    distinguishable difference between these and other uninterpreted
    constants.
    """

    res = z3util.AstSet()
    def rec(e):
        if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            res.add(e)
            return
        for child in e.children():
            rec(child)
    rec(simsym.unwrap(e))
    return res

class IsomorphicMatch(object):
    """Construct an expression that matches isomorphisms of a set of conditions.

    By using the negation of the constructed expression, we can
    enumerate non-isomorphic models."""

    ## XXX handling FDs and timestamps might be better done by treating
    ## them as supporting order, rather than supporting just equality;
    ## the isomorphism condition would be the values being in the same
    ## order, rather than in the same equality pattern.

    def __init__(self):
        # This maps from Interpreter instances to representative maps.
        # A representative map is a dictionary from HashableAst
        # literal values to Z3 expressions that represent those
        # values.
        self.__distinct_realms = collections.defaultdict(dict)
        # Set of isomorphism conditions for value isomorphisms.
        self.__conds = z3util.AstSet()

    def add(self, realm, expr, val, env):
        """Add a condition on the value of expr.

        expr and val must be instances of simsym.Symbolic.  env must
        be a simsym.SymbolicApplyResult that provides the context for
        interpreting constants in expr and val.

        For most expr's, this will require that an isomorphic
        assignment assign val to expr.

        If realm is an Interpreter, then this will require that all
        keys in the Interpreter be distinct, but it will not place
        constraints on their specific values.  This makes it possible
        to match isomorphic "equality patterns" between values of
        uninterpreted sorts, or values we wish to treat as
        uninterpreted.
        """

        if not isinstance(expr, simsym.Symbolic):
            raise TypeError("Expected instance of simsym.Symbolic, got %r" % expr)
        if not isinstance(val, simsym.Symbolic):
            raise TypeError("Expected instance of simsym.Symbolic, got %r" % val)

        if realm is None:
            # Default realm.  Use value equality.
            if not isinstance(expr, simsym.SBool):
                print 'WARNING: Interpreted sort assignment:', \
                    type(expr), expr, val
            self.__conds.add(expr == val)
        elif isinstance(realm, testgen.Interpreter):
            # Use equality isomorphism within this realm
            rep_map = self.__distinct_realms[realm]
            hval = z3util.HashableAst(val)
            rep_map.setdefault(hval, expr)
        else:
            raise ValueError("Unknown realm type %r" % realm)

    def condition(self):
        """Return the isomorphism condition."""
        conds = list(self.__conds)

        for rep_map in self.__distinct_realms.values():
            representatives = rep_map.values()
            if len(representatives) > 1:
                conds.append(simsym.distinct(*representatives))

        return simsym.symand(conds)

def is_idempotent(result):
    """Return whether the calls in test_result can be idempotent.

    This returns a sequence of booleans, where the nth boolean
    indicates if the nth call in every permutation of the callset can
    have no effect on the state.  The "can" is important: if the state
    isn't sufficiently constrained, then it's possible for it to be
    both idempotent and non-idempotent given different assignments of
    unconstrained values.

    If the returned sequence is all 'True', then the call set is
    additionally nullipotent.
    """

    res = [True] * (len(result.value.post_states[0]) - 1)
    for perm_states in result.value.post_states:
        for snum, (s1, s2) in enumerate(zip(perm_states, perm_states[1:])):
            # Is there any satisfying assignment that lets these two
            # states be equivalent?  Note that this may carefully pick
            # internal variables (e.g., time) to make idempotence
            # possible, while other equally valid assignments would
            # not be idempotent.
            check = simsym.check(
                simsym.symand([result.path_condition, s1 == s2]))
            if check.is_unknown:
                print '  Idempotence unknown:', check.reason
                return None
            idem = check.is_sat

            res[snum] = res[snum] and idem

            if False:
                # Also check if it's non-idempotent.  Note that it's often
                # easy to pick internal variables (time, especially) that
                # will cause an operation to be non-idempotent, so we
                # quantify over all internal variables.
                check = simsym.check(
                    simsym.forall(result.internals,
                                  simsym.symand([result.path_condition,
                                                 s1 != s2])))
                notidem = check.is_sat
                # XXX This doesn't seem to hold either way (sat/unsat
                # or unsat/sat), though they're very rarely sat/sat.
                assert not (idem and notidem)

            # Short-circuit
            if not any(res):
                return res
    return res

def idempotent_projs(result, iso_constraint=True):
    """Returns the projections for which each call in result is idempotent.

    This returns a list of idempotence sets, where the entries in the
    list correspond to the calls in result's call set (in the order
    before permutation).  Each idempotence set is a list of
    projections for which that call is idempotent.  This list will be
    empty if the call is not idempotent for any projection.

    A call is considered idempotent for a projection P if there is
    some permutation in which P(state) is equal before and after the
    call and some permutation in which P(state) is distinct before and
    after the call.  Note that this excludes nullipotent projections.

    For projections, this considers all nodes of the state structure,
    recursively.

    result must be the SymbolicApplyResult for the path to consider.
    If this is applied to a particular test case, iso_constraint must
    be the isomorphism constraint produced when generating that test
    case.
    """

    # It seems Z3 often can't solve our idempotence checks.  Oh well.

    root = __import__(args.module).model_class
    pc = result.path_condition
    def xcheck(cond):
        check = simsym.check(simsym.symand([pc, iso_constraint, cond]))
        if check.is_unknown:
            print '  Idempotence unknown:', check.reason
#            print '    ' + str(cond)
        return check

    res = []
    # For each call
    for states in result.value.op_states:
        # Walk all projections
        def walk(typ, proj, label):
            """Walk Symbolic type typ.  proj(state) must retrieve a projected
            value of type typ from state.  label must be a tuple that
            can be joined to describe the current projection.

            Returns a list of projection expressions as strings that
            are idempotent for this call.
            """

            # Build idempotence test for this projection
            did_change, did_not_change = [], []
            for (pre, post) in states:
                # Is there a permutation in which this projection did
                # change across this call?
                did_change.append(proj(pre) != proj(post))
                # And is there a permutation in which this projection
                # did not change across this call?
                did_not_change.append(proj(pre) == proj(post))
            idem_expr = simsym.symand([simsym.symor(did_change),
                                       simsym.symor(did_not_change)])

            check = xcheck(idem_expr)
            res = []
            if check.is_sat:
                # This projection is idempotent
                res.append(''.join(label))
                # We continue to descend because the more detailed
                # projection information is often useful in
                # understanding why a call is idempotent.

            # Break down the projection further
            if issubclass(typ, simsym.SStructBase):
                # Are any fields idempotent?
                for fname, ftyp in typ._fields.items():
                    res.extend(walk(ftyp,
                                    lambda state, fname=fname:
                                    getattr(proj(state), fname),
                                    label + ('.' + fname,)))
            elif issubclass(typ, simsym.SMapBase):
                # Is there some map value that is idempotent?  Because
                # of how we construct the final query, this requires
                # it to have the same index in all permutations.
                idx = typ._indexType.var()
                res.extend(walk(typ._valueType,
                                lambda state: proj(state)[idx],
                                label + ('[?]',)))
            return res

        idem_projs = walk(root, lambda x:x, ('state',))
        res.append(idem_projs)
    return res

class TestWriter(object):
    def __init__(self, trace_file, model_file, test_file, testgen):
        if isinstance(trace_file, basestring):
            trace_file = open(trace_file, 'w')
        self.trace_file, self.model_file, self.test_file \
            = trace_file, model_file, test_file
        if test_file and testgen:
            self.testgen = testgen(test_file)
        else:
            self.testgen = None

        # model_data schema:
        #   root     -> {'tests': {callsetname: {pathid: pathinfo}}}
        #   callsetname -> '_'-joined call names
        #   pathinfo -> {'id': pathname,
        #                'diverge': '' | 'state' | 'results' | 'results state',
        #                'idempotent': [bool],
        #                'tests': [testinfo]}
        #   pathname -> callsetname '_' pathid
        #   testinfo -> {'id': testname,
        #                'assignments': {expr: val},
        #                'idempotent_projs': [[string]]}
        #   testname -> pathname '_' testnum
        self.model_data = {'tests':{}}

    def begin_call_set(self, callset):
        if self.trace_file:
            print >> self.trace_file, "==== Call set %s ====" % \
                " ".join(c.__name__ for c in callset)
            print >> self.trace_file

        self.model_data_callset = collections.OrderedDict()
        self.model_data['tests']['_'.join(c.__name__ for c in callset)] \
            = self.model_data_callset

        self.callset = callset
        self.npath = self.ncompath = self.nmodel = 0

        if self.testgen:
            self.testgen.begin_call_set(callset)

    def keep_going(self):
        return self.nmodel < args.max_testcases

    def on_result(self, result):
        self.npath += 1

        self.model_data_callset[result.pathid] = collections.OrderedDict([
            ('id', ('_'.join(c.__name__ for c in self.callset) +
                    '_' + result.pathid)),
            ('diverge', ' '.join(result.value.diverge)),
            ('idempotent', is_idempotent(result)),
        ])

        # Filter out non-commutative results
        if result.value.diverge != ():
            return

        self.ncompath += 1

        if not self.trace_file and not self.testgen:
            return

        if self.trace_file:
            print >> self.trace_file, "=== Path %s ===" % result.pathid
            print >> self.trace_file

        e = result.path_condition

        ## This can potentially reduce the number of test cases
        ## by, e.g., eliminating irrelevant variables from e.
        ## The effect doesn't seem significant: one version of Fs
        ## produces 3204 test cases without simplify, and 3182 with.
        e = simsym.simplify(e)

        if args.verbose_testgen:
            print "Simplified path condition:"
            print e

        # Find the uninterpreted constants in the path condition.  We
        # omit assumptions because uninterpreted constants that appear
        # only in assumptions generally don't represent that the model
        # actually "touched".  We use the simplified expression
        # because the final state comparison in original expression
        # contains a lot of trivial expressions like x==x for all
        # state variables x, and we don't care about these
        # uninterpreted constants.
        e_vars = expr_vars(
            simsym.simplify(
                simsym.symand(
                    result.get_path_condition_list(
                        with_assume=False, with_det=True))))

        if self.testgen:
            self.testgen.begin_path(result)

        self.model_data_testinfo_list = []
        self.model_data_callset[result.pathid]['tests'] \
            = self.model_data_testinfo_list

        self.npathmodel = 0
        self.last_assignments = None
        while self.keep_going() and self.npathmodel < args.max_tests_per_path:
            # XXX Would it be faster to reuse the solver?
            check = simsym.check(e)
            if check.is_unsat: break
            if check.is_unknown:
                # raise Exception('Cannot enumerate: %s' % str(e))
                print 'Cannot enumerate, moving on..'
                print 'Failure reason:', check.reason
                break

            if 'array-ext' in check.z3_model.sexpr():
                # Work around some non-deterministic bug that causes
                # Z3 to occasionally produce models containing
                # 'array-ext' applications that break evaluation.
                print 'Warning: Working around array-ext bug'
                for i in range(10):
                    check = simsym.check(e)
                    if 'array-ext' not in check.z3_model.sexpr():
                        break
                else:
                    print 'Workaround failed; this won\' end well'

            if args.verbose_testgen:
                print "Model:"
                print check.model

            testinfo = collections.OrderedDict(
                id=('_'.join(c.__name__ for c in self.callset) +
                    '_' + result.pathid + '_' + str(self.npathmodel)),
            )
            self.model_data_testinfo_list.append(testinfo)

            assignments = self.__on_model(result, check.z3_model, e)
            if assignments is None:
                break
            if args.verbose_testgen:
                print 'Assignments:'
                pprint.pprint(assignments)
            if args.diff_testgen:
                new_assignments = {}
                if self.last_assignments is not None:
                    for aexpr, val in assignments:
                        hexpr = z3util.HashableAst(aexpr)
                        sval = str(val)
                        last_sval = self.last_assignments.get(hexpr)
                        if last_sval is not None and last_sval != sval:
                            print '%s: %s -> %s' % (aexpr, last_sval, sval)
                        new_assignments[hexpr] = sval
                self.last_assignments = new_assignments

            testinfo['assignments'] = {}
            for aexpr, val in assignments[None]:
                testinfo['assignments'][str(aexpr)] = str(val)

            # Construct the isomorphism condition for the assignments
            # used by testgen.  This tells us exactly what values
            # actually mattered to test case generation.  However,
            # this set isn't perfect: testgen may have queried
            # assignments that didn't actually matter to the
            # function's behavior (e.g., flags that didn't matter
            # because the function will return an error anyway, etc).
            # To filter out such uninterpreted constants, we only
            # consider those that were *both* used in an assignment by
            # testgen and appeared in the path condition expression.
            # XXX We should revisit this and see how much difference
            # this makes.
            same = IsomorphicMatch()
            for realm, rassigns in assignments.iteritems():
                for aexpr, val in rassigns:
                    aexpr_vars = expr_vars(aexpr)
                    if not aexpr_vars.isdisjoint(e_vars):
                        same.add(realm, aexpr, val, result)
                    elif args.verbose_testgen:
                        print 'Ignoring assignment:', (aexpr, val)
            isocond = same.condition()

            # Compute idempotent projections for this test
            if args.idempotent_projs:
                testinfo['idempotent_projs'] = idempotent_projs(result, isocond)

            # Construct constraint for next test
            notsame = simsym.symnot(isocond)
            if args.verbose_testgen:
                print 'Negation', self.nmodel, ':', notsame
            e = simsym.symand([e, notsame])

        if self.npathmodel == args.max_tests_per_path:
            print '  Max tests reached for path %s' % result.pathid

        if self.testgen:
            self.testgen.end_path()

    def __on_model(self, result, model, constraint):
        self.nmodel += 1
        res = None

        if self.trace_file:
            print >> self.trace_file, "== Path %s model %d ==" % \
                (result.pathid, self.npathmodel)
            print >> self.trace_file, model.sexpr()
            print >> self.trace_file
            self.trace_file.flush()

        if self.testgen:
            smodel = result.get_model(model)
            smodel.track_assignments(True)
            self.testgen.on_model(smodel, constraint)
            res = smodel.assignments()

        self.npathmodel += 1
        return res

    def end_call_set(self):
        if self.testgen:
            self.testgen.end_call_set()

    def finish(self):
        if self.testgen:
            self.testgen.finish()
        if self.model_file is not None:
            json.dump(self.model_data, file(self.model_file, 'w'), indent=2)

parser = argparse.ArgumentParser()
parser.add_argument('-c', '--check-conds', action='store_true',
                    help='Check commutativity conditions for sat/unsat')
parser.add_argument('-p', '--print-conds', action='store_true',
                    help='Print commutativity conditions')
parser.add_argument('-m', '--model-file',
                    help='Z3 model output file')
parser.add_argument('--trace-file',
                    help='User-readable Z3 model trace output file')
parser.add_argument('-t', '--test-file',
                    help='Test generator output file')
parser.add_argument('-n', '--ncomb', type=int, default=2, action='store',
                    help='Number of system calls to combine per test')
parser.add_argument('-f', '--functions', action='store',
                    help='Methods to run (e.g., stat,fstat).  Accepts x/y to \
                    specify call sets, {x,y} for grouping, * for all calls, and \
                    any combination of these.  All single calls will be \
                    collected into combinations of size NCOMB.')
parser.add_argument('--simplify-more', default=False, action='store_true',
                    help='Use ctx-solver-simplify')
parser.add_argument('--max-testcases', type=int, default=sys.maxint, action='store',
                    help='Maximum # test cases to generate per call set')
parser.add_argument('--max-tests-per-path', type=int, default=sys.maxint,
                    help='Maximum # test cases to generate per path')
parser.add_argument('--verbose-testgen', default=False, action='store_true',
                    help='Print diagnostics during model enumeration')
parser.add_argument('--diff-testgen', default=False, action='store_true',
                    help='Print variables that change during enumeration')
parser.add_argument('--idempotent-projs', default=False, action='store_true',
                    help='Record idempotent projections in model file (slow)')
parser.add_argument('module', metavar='MODULE', default='fs', action='store',
                    help='Module to test (e.g., fs)')

def print_cond(msg, cond):
    if args.check_conds and simsym.check(cond).is_unsat:
        return

    ## If the assumptions (i.e., calls to simsym.assume) imply the condition
    ## is true, we say that condition always holds, and we can print "always".
    ## It would be nice to print a clean condition that excludes assumptions,
    ## even if the assumptions don't directly imply the condition, but that
    ## would require finding the simplest expression for x such that
    ##
    ##   x AND simsym.assume_list = cond
    ##
    ## which seems hard to do using Z3.  In principle, this should be the
    ## same as simplifying the 'c' expression below, but Z3 isn't good at
    ## simplifying it.  We could keep the two kinds of constraints (i.e.,
    ## explicit assumptions vs. symbolic execution control flow constraints)
    ## separate in simsym, which will make them easier to disentangle..

    #c = simsym.implies(simsym.symand(simsym.assume_list), cond)
    ## XXX the above doesn't work well -- it causes open*open to say "always".
    ## One hypothesis is that we should be pairing the assume_list with each
    ## path condition, instead of taking the assume_list across all paths.
    c = cond

    if args.check_conds and simsym.check(simsym.symnot(c)).is_unsat:
        s = 'always'
    else:
        if args.print_conds:
            scond = simsym.simplify(cond, args.simplify_more)
            s = '\n    ' + str(scond).replace('\n', '\n    ')
        else:
            if args.check_conds:
                s = 'sometimes'
            else:
                s = 'maybe'
    print '  %s: %s' % (msg, s)

def parse_functions(functions, ncomb, module):
    """Parse a functions string, returning a list of callsets."""

    base = module.model_class
    callnames = {name for name in dir(base)
                 if getattr(getattr(base, name), 'is_model_function', False)}
    if functions is None:
        functions = '*'
    chars = list(functions)

    def consume(char):
        if chars and chars[0] == char:
            return chars.pop(0)
    def parse_list():
        callsets = parse_set()
        while consume(','):
            callsets.extend(parse_set())
        return callsets
    def parse_set():
        callsets = parse_call()
        while consume('/'):
            ncallsets = []
            for cs2 in parse_call():
                for cs1 in callsets:
                    ncallsets.append(cs1 + cs2)
            callsets = ncallsets
        return callsets
    def parse_call():
        if not chars:
            raise ValueError('Expected call name, found nothing')
        if consume('{'):
            res = parse_list()
            if not consume('}'):
                raise ValueError('Open brace with no close brace')
            return res
        if consume('*'):
            return [[c] for c in callnames]
        callname = ''
        while chars and chars[0] not in '{},/*':
            callname += chars.pop(0)
        if callname not in callnames:
            raise ValueError('Unknown call %r' % callname)
        return [[callname]]

    try:
        callsets = parse_list()
        if chars:
            raise ValueError('Syntax error')
    except ValueError as e:
        raise
        pos = len(functions) - len(chars) + 1
        raise ValueError('%s\n%s\n%s' % (e, functions, ' '*(pos - 1) + '^'))

    # Expand single calls
    ncallsets, singles = [], []
    for callset in callsets:
        if len(callset) > 1:
            ncallsets.append(callset)
        else:
            singles.append(callset[0])
    ncallsets.extend(itertools.combinations_with_replacement(singles, ncomb))

    # Canonicalize order of each callset and then all callsets
    ncallsets = sorted(sorted(callset) for callset in ncallsets)
    return ncallsets

def main(spec_args):
    global args                 # XXX Get rid of this global
    args = spec_args

    z3printer._PP.max_lines = float('inf')
    m = __import__(args.module)
    testgen = m.model_testgen if hasattr(m, 'model_testgen') else None
    if testgen is None and args.test_file:
        parser.error("No test case generator for this module")

    test_writer = TestWriter(args.trace_file, args.model_file, args.test_file,
                             testgen)

    for callset in parse_functions(args.functions, args.ncomb, m):
        calls = [getattr(m.model_class, callname) for callname in callset]
        do_callset(m.model_class, calls, test_writer)

    test_writer.finish()

def do_callset(base, callset, test_writer):
    print ' '.join([c.__name__ for c in callset])
    test_writer.begin_call_set(callset)

    reporter = progress.ProgressReporter(
        '  {0.npath} paths ({0.ncompath} commutative), {0.nmodel} testcases',
        test_writer)

    condlists = collections.defaultdict(list)
    terminated = False
    diverged = set()
    all_internals = []
    for sar in simsym.symbolic_apply(test, base, *callset):
        is_commutative = (sar.value.diverge == ())
        diverged.update(sar.value.diverge)
        condlists[is_commutative].append(sar.path_condition)
        all_internals.extend(sar.internals)
        test_writer.on_result(sar)
        if not test_writer.keep_going():
            terminated = True
            break

    test_writer.end_call_set()
    reporter.end()

    if terminated:
        print '  enumeration incomplete; skipping conditions'
        return

    conds = collections.defaultdict(lambda: [simsym.wrap(z3.BoolVal(False))])
    for result, condlist in condlists.items():
        conds[result] = condlist

    if True in condlists:
        commute = simsym.symor(condlists[True])
        # Internal variables help deal with situations where, for the
        # same assignment of initial state + external inputs, two
        # operations both can commute and can diverge (depending on
        # internal choice, like the inode number for file creation).
        cannot_commute = simsym.symnot(simsym.exists(all_internals, commute))
        print_cond('can commute', commute)
    else:
        cannot_commute = True

    if False in condlists:
        diverge = simsym.symor(condlists[False])
        print_cond('cannot commute; %s can diverge' % ', '.join(diverged),
                   simsym.symand([diverge, cannot_commute]))

if __name__ == "__main__":
    main(parser.parse_args())
