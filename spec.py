#!/usr/bin/env python

import simtest
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
import testgen
import traceback
import importlib

# A test module must have the following two attributes:
#
# * model_class must be the state class whose methods are the
#   operations to test.  The test operations must be decorated with
#   @model.methodwrap.
#
# * model_testgen (optional) must be the test generator class for this
#   model.  It should subclass and implement testgen.TestGenerator.
#   If this attribute is not present, tests cannot be generated.

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
        if not z3.is_ast(e):
            return
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
        # For conditions subject to equality isomorphism, this maps
        # from realms (specifically, Interpreter instances) to
        # equivalence classes of expressions.  Each equivalence class
        # contains the set of known expressions that evaluate to the
        # same literal value.  Specifically,
        #   {Interpreter: RepMap}
        #   RepMap := {HashableAst literal (e.g., 2 or f!0): Reps}
        #   Reps   := AstSet of expressions that evaluate to the representative
        self.__repmaps = collections.defaultdict(
            lambda: collections.defaultdict(z3util.AstSet))
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
            hval = z3util.HashableAst(val)
            self.__repmaps[realm][z3util.HashableAst(val)].add(expr)
        else:
            raise ValueError("Unknown realm type %r" % realm)

    def condition(self):
        """Return the isomorphism condition."""
        conds = list(self.__conds)

        for rep_map in self.__repmaps.itervalues():
            distinct = []
            for reps in rep_map.itervalues():
                reps = list(reps)
                # Require each representative group to be distinct
                distinct.append(reps[0])
                # Require all expressions within the representative
                # group to be equal
                conds.append(simsym.symeq(*reps))
            if len(distinct) > 1:
                conds.append(simsym.distinct(*distinct))

        return simsym.symand(conds)

def idempotent_projs(result, iso_constraint=True):
    """Returns the projections for which each call in result is idempotent.

    This returns two values.  The first is a list of idempotence sets,
    where the entries in the list correspond to the calls in result's
    call set (in the order before permutation).  Each idempotence set
    is a list of projections for which that call is idempotent.  The
    idempotence set will be empty if the call is not idempotent for
    any projection.  The second returned value is a count of the
    number of projections that this failed to resolve the idempotence
    of.

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

    root = importlib.import_module(args.module).model_class
    pc = result.path_condition
    unknown_count = [0]
    def xcheck(cond):
        check = simsym.check(simsym.symand([pc, iso_constraint, cond]))
        if check.is_unknown:
            if unknown_count[0] == 0:
                print '  Idempotence unknown:', check.reason
#                print '    ' + str(cond)
            unknown_count[0] += 1
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
    return res, unknown_count[0]

class TestWriter(simtest.ExecutionMonitorBase):
    def __init__(self, trace_file, model_file, test_file, testgen):
        super(TestWriter, self).__init__()
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
        #                'exception': string,
        #                'diverge': '' | string,
        #                'tests': [testinfo],
        #                'testerror'?: string}
        #     Either 'exception' or 'diverge' will be present.
        #     'testerror' gives the error that terminated test
        #     generation for this path (if any).
        #   pathname -> callsetname '_' pathid
        #   testinfo -> {'id': testname,
        #                'assignments': {expr: val},
        #                'idempotent_projs': [[string]],
        #                'idempotence_unknown': int}  # if non-zero
        #   testname -> pathname '_' testnum
        self.model_data = {'tests':{}}

        self.nmodel = self.nerror = self.ntesterrors = 0

    def get_progress_format(self):
        return '{0.nmodel} testcases (errors: {0.nerror} model, {0.ntesterrors} testgen)'

    def begin_call_set(self, callset):
        super(TestWriter, self).begin_call_set(callset)
        if self.trace_file:
            print >> self.trace_file, "==== Call set %s ====" % \
                " ".join(self.callset_names)
            print >> self.trace_file

        self.model_data_callset = collections.OrderedDict()
        self.model_data['tests']['_'.join(c.__name__ for c in callset)] \
            = self.model_data_callset

        self.nmodel = self.nerror = self.ntesterrors = 0

        if self.testgen:
            self.testgen.begin_call_set(callset)

    def stop_call_set(self):
        if self.testgen and self.testgen.stop_call_set():
            return True
        return self.nmodel >= args.max_testcases

    def _testerror(self, reason, pathinfo):
        pathinfo['testerror'] = reason
        print 'Cannot enumerate, moving on..'
        print 'Failure reason:', reason
        self.ntesterrors += 1

    def on_path(self, result):
        super(TestWriter, self).on_path(result)

        pathinfo = collections.OrderedDict([
            ('id', '_'.join(self.callset_names) + '_' + result.pathid)])
        self.model_data_callset[result.pathid] = pathinfo

        if result.type == 'exception':
            pathinfo['exception'] = '\n'.join(
                traceback.format_exception_only(*result.exc_info[:2]))
            self.nerror += 1
            return

        pathinfo['diverge'] = ', '.join(map(str, result.value.diverge))

        # Filter out non-commutative results
        if len(result.value.diverge):
            return

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

        if self.trace_file:
            print >> self.trace_file, e
            print >> self.trace_file

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
        pathinfo['tests'] = self.model_data_testinfo_list

        self.npathmodel = 0
        self.last_assignments = None
        while not self.stop_call_set() and \
              self.npathmodel < args.max_tests_per_path:
            # XXX Would it be faster to reuse the solver?
            check = simsym.check(e)
            if check.is_sat and 'array-ext' in check.z3_model.sexpr():
                # Work around some non-deterministic bug that causes
                # Z3 to occasionally produce models containing
                # 'array-ext' applications that break evaluation.
                print 'Warning: Working around array-ext bug'
                for i in range(10):
                    check = simsym.check(e)
                    if not check.is_sat:
                        continue
                    if 'array-ext' not in check.z3_model.sexpr():
                        break
                else:
                    self._testerror('array-ext workaround failed', pathinfo)
                    break

            if check.is_unsat: break
            if check.is_unknown:
                # raise Exception('Cannot enumerate: %s' % str(e))
                self._testerror(check.reason, pathinfo)
                break

            if args.verbose_testgen:
                print "Model:"
                print check.model

            testid = ('_'.join(self.callset_names) +
                      '_' + result.pathid + '_' + str(self.npathmodel))
            testinfo = collections.OrderedDict(id=testid)
            self.model_data_testinfo_list.append(testinfo)

            assignments = self.__on_model(result, check.z3_model, e, testid)
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
                projs, proj_errors = idempotent_projs(result, isocond)
                testinfo['idempotent_projs'] = projs
                if proj_errors:
                    testinfo['idempotence_unknown'] = proj_errors

            # Construct constraint for next test
            notsame = simsym.symnot(isocond)
            if args.verbose_testgen:
                print 'Negation', self.nmodel, ':', notsame
            e = simsym.symand([e, notsame])

        if self.npathmodel == args.max_tests_per_path:
            print '  Max tests reached for path %s' % result.pathid

        if self.testgen:
            self.testgen.end_path()

    def __on_model(self, result, model, constraint, testid):
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
            self.testgen.on_model(testid, smodel, constraint)
            res = smodel.assignments()

        self.npathmodel += 1
        return res

    def end_call_set(self):
        super(TestWriter, self).end_call_set()
        if self.testgen:
            self.testgen.end_call_set()

    def finish(self):
        super(TestWriter, self).finish()
        if self.testgen:
            self.testgen.finish()
        if self.model_file is not None:
            json.dump(self.model_data, file(self.model_file, 'w'), indent=2)

parser = argparse.ArgumentParser()
parser.add_argument('-c', '--check-conds', action='store_true',
                    help='Check commutativity conditions for sat/unsat')
parser.add_argument('-p', '--print-conds', action='store_true',
                    help='Print commutativity conditions')
parser.add_argument('-pp', '--pretty-print-conds', action='store_const',
                    dest='print_conds', const='simplify',
                    help='Print commutativity conditions with aggressive \
                    simplification')
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
                    specify call sets, {x,y} for grouping, * for all calls, \
                    !set to negate a set, and any combination of these. \
                    All single calls will be collected into combinations of \
                    size NCOMB.')
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
                    help='Module to test (e.g., models.fs)')

def parse_functions(functions, ncomb, module):
    """Parse a functions string, returning a list of callsets."""

    base = module.model_class
    callnames = {name for name in dir(base)
                 if getattr(getattr(base, name), 'is_model_function', False)}
    if functions is None:
        functions = '*'
    chars = list(functions)

    # list -> set ("," set)*
    # set  -> "!"? call ("/" call)*
    # call -> ("{" list "}") | "*" | callname
    def consume(char):
        if chars and chars[0] == char:
            return chars.pop(0)
    def parse_list():
        callsets, anti = parse_set()
        while consume(','):
            ncallsets, nanti = parse_set()
            callsets.extend(ncallsets)
            anti.extend(nanti)
        if not callsets and anti:
            callsets = [[c] for c in callnames]
        for callset in anti:
            if callset in callsets:
                callsets.remove(callset)
        return callsets
    def parse_set():
        invert = consume('!')
        callsets = parse_call()
        while consume('/'):
            ncallsets = []
            for cs2 in parse_call():
                for cs1 in callsets:
                    ncallsets.append(cs1 + cs2)
            callsets = ncallsets
        return (callsets, []) if not invert else ([], callsets)
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
        return [[parse_callname()]]
    def parse_callname():
        callname = ''
        while chars and chars[0] not in '!{},/*':
            callname += chars.pop(0)
        if callname not in callnames:
            raise ValueError('Unknown call %r' % callname)
        return callname

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
    m = importlib.import_module(args.module)
    testgen = m.model_testgen if hasattr(m, 'model_testgen') else None
    if testgen is None and args.test_file:
        parser.error("No test case generator for this module")

    test_writer = TestWriter(args.trace_file, args.model_file, args.test_file,
                             testgen)

    for callset in parse_functions(args.functions, args.ncomb, m):
        calls = [getattr(m.model_class, callname) for callname in callset]
        simtest.test_callset(m.model_class, calls, [test_writer],
                             check_conds=args.check_conds,
                             print_conds=args.print_conds)

    test_writer.finish()

if __name__ == "__main__":
    main(parser.parse_args())
