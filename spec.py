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

# A test module must have the following three attributes:
#
# * model_class must be the state class whose methods are the
#   operations to test.  The test operations must be decorated with
#   @model.methodwrap.
#
# * model_testgen (optional) must be the test generator class for this
#   model.  It should subclass and implement testgen.TestGenerator.
#   If this attribute is not present, tests cannot be generated.
#
# * isomorphism_types (optional) is a dictionary overriding the
#   default isomorphism types used by IsomorphicMatch during test
#   enumeration.  By default, uninterpreted types are constrained only
#   by equality and all other types are concrete-valued.  In
#   particular, it's often necessary to treat integer types like
#   uninterpreted types or to ignore them entirely to avoid infinite
#   enumeration during test generation.  isomorphism_types maps from
#   Symbolic types to one of:
#
#   - "ignore", if values of this type should be ignored altogether
#     when enumerating models.
#
#   - "equal", if values of this type should be constrained only by
#     their pattern of equality (like an uninterpreted sort).
#
#   At present, the Symbolic type can only be a primitive type or a
#   synonym for a primitive type, since isomorphism will destructure
#   any compound types before checking this.

TestResult = collections.namedtuple(
    'TestResult', 'diverge results post_states op_states')

def test(base, *calls):
    # XXX This codifies "regular" commutativity, not strong
    # commutativity.  They're equivalent for pairs, which is all we
    # use in the paper, but we should fix this.

    init = base.var(base.__name__)

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
        seqname = ''.join(map(lambda i: chr(i + ord('a')), callseq))
        for idx in callseq:
            callname = chr(idx + ord('a'))
            # Include the sequence and call name in all anonymous
            # variable names
            simsym.anon_info = '_seq' + seqname + '_call' + callname
            r[idx] = calls[idx](s, callname)
            snapshot = s.copy()
            post_states[-1].append(snapshot)
            op_states[idx].append((prestate, snapshot))
            prestate = snapshot
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

    def __init__(self, isomorphism_types={}):
        self.__isomorphism_types = isomorphism_types

        # This maps from the simsym.Symbolic subclass of each type
        # with "equal" isomorphism type to representative maps.  A
        # representative map is a dictionary from HashableAst value to
        # the Z3 expression that represents that value.
        self.__representatives = collections.defaultdict(dict)
        # Set of isomorphism conditions, except for representative
        # distinctness.
        self.__conds = z3util.AstSet()

    def add(self, expr, val, env):
        """Add a condition on the value of expr.

        expr and val must be instances of simsym.Symbolic.  env must
        be a simsym.SymbolicApplyResult that provides the context for
        interpreting constants in expr and val.

        For most expr's, this will require that an isomorphic
        assignment assign val to expr.

        If expr's sort is uninterpreted or has isomorphism type
        "equal", then expr's of the same sort will be grouped into
        equivalence classes by val and the isomorphism assignment will
        require that these expr's form the same equivalence classes.

        If expr's sort has isomorphism type "ignore", then this
        condition will be ignored.

        Before adding any expr that uses an uninterpreted value, the
        caller must add an expr that is equal to that uninterpreted
        value.  (This happens naturally when conditions are added in
        the order they arise during test generation.)
        """

        if not isinstance(expr, simsym.Symbolic):
            raise TypeError("Expected instance of simsym.Symbolic, got %r" % expr)
        if not isinstance(val, simsym.Symbolic):
            raise TypeError("Expected instance of simsym.Symbolic, got %r" % val)

        # Resolve the isomorphism type of expr
        symtype = type(expr)
        isomorphism_type = self.__get_iso_type(symtype)
        if isomorphism_type == None and not issubclass(symtype, simsym.SBool):
            print 'WARNING: Interpreted sort assignment:', type(expr), expr, val

        # Don't bother with rewriting and such if we're going to
        # ignore this condition anyway
        if isomorphism_type == "ignore":
            return

        z3expr, z3val = simsym.unwrap(expr), simsym.unwrap(val)

        # Rewrite expression to use representatives.  The requirement
        # on the order that the caller adds conditions means that
        # we'll always have a representative for uninterpreted values
        # in expr.  This also means we never have to worry about
        # cyclic representatives (where the representative expression
        # depends on some uninterpreted value whose representative
        # depends on the first representative).
        rexpr = self.__rewrite(z3expr, symtype, env)
        if rexpr is None:
            return

        # Register representative expressions.  We do this after
        # rewriting the expression so we won't have uninterpreted
        # values in the representative expression.
        if isomorphism_type == "equal":
            hval = z3util.HashableAst(z3val)
            self.__representatives[symtype].setdefault(hval, rexpr)

        # Rewrite the value to use representatives.  We do this
        # after registering representative expressions in case we
        # just registered the representative for this value.
        rval = self.__rewrite(z3val, symtype, env)
        if rval is None:
            return

        # Handle assignment
        if isomorphism_type == "equal" or isomorphism_type == None:
            self.__conds.add(rexpr == rval)
        else:
            raise ValueError("Unknown isomorphism type %r" % isomorphism_type)

    def __get_iso_type(self, symtype):
        """Return the isomorphism type of symtype."""

        for cls in symtype.__mro__:
            if cls in self.__isomorphism_types:
                return self.__isomorphism_types[cls]

        kind = symtype._z3_sort().kind()
        if kind == z3.Z3_UNINTERPRETED_SORT:
            return "equal"
        return None

    def __rewrite(self, expr, symtype, env):
        """Replace uninterpreted values in expr with their representatives.

        env must be a simsym.SymbolicApplyResult that provides the
        environment for this rewriting.
        """

        # The expression may consist of constants and selects.  We
        # need to map every select index to its Symbolic type to
        # figure out its isomorphism type, so we unwind the whole
        # expression, get the pseudo-Symbolic type of the base
        # constant, and use this to work out the types of the indexes.

        class Ignore(Exception): pass

        def rec(expr):
            if z3.is_select(expr):
                array, idx = expr.children()
                array2, pseudo_type = rec(array)
                idx2 = rewrite_const(idx, pseudo_type[0], True)
                return array2[idx2], pseudo_type[1]
            elif z3.is_const(expr):
                return expr, env.symbolic_type(expr)
            else:
                raise Exception("Unexpected AST type %r" % expr)

        def rewrite_const(const, symtype, is_index):
            rep = self.__representatives[symtype].get(z3util.HashableAst(const))
            if rep is not None:
                if args.verbose_testgen:
                    print "Replacing", const, "of type", symtype, "with", rep
                return rep
            elif const.sort().kind() == z3.Z3_UNINTERPRETED_SORT and \
                 '!' in str(const):
                # This is one of the Z3-generated values from this
                # sort's universe.
                if is_index:
                    # This is used as an array index.  Since there's
                    # no expression actually equal to this index
                    # value, there's no way this value of the array
                    # can matter, so we just ignore it.
                    if args.verbose_testgen:
                        print "Ignoring unrepresented index in", expr
                    raise Ignore()
                # If this was not just an array index, we can't
                # express an isomorphism.
                raise Exception("No representative for %r in %r" %
                                (const, expr))
            else:
                # No transformation
                return const

        if z3.is_const(expr):
            # If we're called with a constant, it could be something
            # like z3.IntNumRef(42), which doesn't carry enough of its
            # own type information for us to resolve it bottom-up, but
            # we do know its type from the top down.
            return rewrite_const(expr, symtype, False)
        else:
            # If we're not called with a constant, it must be a
            # select, in which case the recursive base of the select
            # must be an uninterpreted constant, which we can resolve
            # type information for bottom-up.  Ugh.
            try:
                return rec(expr)[0]
            except Ignore:
                return None

    @staticmethod
    def __xand(exprs):
        if len(exprs) == 0:
            return True
        return z3.And(exprs)

    def __same_cond(self):
        conds = list(self.__conds)

        for rep_map in self.__representatives.values():
            representatives = rep_map.values()
            if len(representatives) > 1:
                conds.append(z3.Distinct(representatives))

        return self.__xand(conds)

    def notsame_cond(self):
        return simsym.wrap(z3.Not(self.__same_cond()))

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
            idem_z3, m = simsym.check(
                simsym.symand([result.path_condition, s1 == s2]))
            if idem_z3 == z3.unknown:
                print '  Idempotence unknown:', m
                return None
            idem = (idem_z3 == z3.sat)

            res[snum] = res[snum] and idem

            if False:
                # Also check if it's non-idempotent.  Note that it's often
                # easy to pick internal variables (time, especially) that
                # will cause an operation to be non-idempotent, so we
                # quantify over all internal variables.
                notidem_z3, m2 = simsym.check(
                    simsym.forall(result.internals,
                                  simsym.symand([result.path_condition,
                                                 s1 != s2])))
                notidem = (notidem_z3 == z3.sat)
                # XXX This doesn't seem to hold either way (sat/unsat
                # or unsat/sat), though they're very rarely sat/sat.
                assert not (idem and notidem)

            # Short-circuit
            if not any(res):
                return res
    return res

def idempotent_projs(result):
    """Returns the projections for which each call in result is idempotent.

    This returns a list of idempotence sets, where the entries in the
    list correspond to the calls in result's call set (in the order
    before permutation).  Each idempotence set is a list of
    projections for which that call is idempotent.  This list will be
    empty if the call is not idempotent for any projection.

    A call is considered idempotent for a projection P if there is
    some permutation in which P(state) is equal before and after the
    call and some permutation in which P(state) is distinct before and
    after the operation.  Note that this excludes nullipotent
    projections.

    For projections, this considers all nodes of the state structure,
    recursively.
    """

    # It seems Z3 often can't solve our idempotence checks.  Oh well.

    root = __import__(args.module).model_class
    pc = result.path_condition
    def check(cond):
        res, m = simsym.check(simsym.symand([pc, cond]))
        if res == z3.unknown:
            print '  Idempotence unknown:', m
            print '    ' + str(cond)
        return res, m

    res = []
    # For each call
    for states in result.value.op_states:
        # Walk all projections
        def walk(typ, proj, label):
            """Walk Symbolic type typ.  proj(state) must retrieve a projected
            value of type typ from state.  label must be a tuple that
            can be joined to describe the current projection.
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

            sat_z3, m = check(idem_expr)
            if sat_z3 == z3.sat:
                # This projection is idempotent
                # XXX We might still want to descend.  More detailed
                # leaf information can be useful.
                return [''.join(label)]

            # Try breaking down the projection further
            if issubclass(typ, simsym.SStructBase):
                # Are any fields idempotent?
                idem_projs = []
                for fname, ftyp in typ._fields.items():
                    idem_projs.extend(walk(ftyp,
                                           lambda state, fname=fname:
                                           getattr(proj(state), fname),
                                           label + ('.' + fname,)))
                return idem_projs
            elif issubclass(typ, simsym.SMapBase):
                # Is there some map value that is idempotent?  Because
                # of how we construct the final query, this requires
                # it to have the same index in all permutations.
                idx = typ._indexType.var()
                return walk(typ._valueType,
                            lambda state: proj(state)[idx],
                            label + ('[?]',))
            else:
                return []

        idem_projs = walk(root, lambda x:x, ('state',))
        res.append(idem_projs)
    return res

class TestWriter(object):
    def __init__(self, trace_file, model_file, test_file, testgen,
                 isomorphism_types):
        if isinstance(trace_file, basestring):
            trace_file = open(trace_file, 'w')
        self.trace_file, self.model_file, self.test_file \
            = trace_file, model_file, test_file
        if test_file and testgen:
            self.testgen = testgen(test_file)
        else:
            self.testgen = None
        self.isomorphism_types = isomorphism_types

        # model_data schema:
        #   root     -> {'tests': {callsetname: {pathid: pathinfo}}}
        #   callsetname -> '_'-joined call names
        #   pathinfo -> {'id': pathname,
        #                'diverge': '' | 'state' | 'results' | 'results state',
        #                'idempotent': [bool],
        #                'idempotent_projs': [[string]],
        #                'tests': [testinfo]}
        #   pathname -> callsetname '_' pathid
        #   testinfo -> {'id': testname, 'assignments': {expr: val}}
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

        if args.idempotent_projs:
            self.model_data_callset[result.pathid]['idempotent_projs'] \
                = idempotent_projs(result)

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
            check, model = simsym.check(e)
            if check == z3.unsat: break
            if check == z3.unknown:
                # raise Exception('Cannot enumerate: %s' % str(e))
                print 'Cannot enumerate, moving on..'
                print 'Failure reason:', model
                break

            if check == z3.sat and 'array-ext' in model.sexpr():
                # Work around some non-deterministic bug that causes
                # Z3 to occasionally produce models containing
                # 'array-ext' applications that break evaluation.
                print 'Warning: Working around array-ext bug'
                for i in range(10):
                    check, model = simsym.check(e)
                    if 'array-ext' not in model.sexpr():
                        break
                else:
                    print 'Workaround failed; this won\' end well'

            if args.verbose_testgen:
                print "Model:"
                print model

            testinfo = collections.OrderedDict(
                id=('_'.join(c.__name__ for c in self.callset) +
                    '_' + result.pathid + '_' + str(self.npathmodel)),
            )
            self.model_data_testinfo_list.append(testinfo)

            assignments = self.__on_model(result, model)
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
            for aexpr, val in assignments:
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
            same = IsomorphicMatch(self.isomorphism_types)
            for aexpr, val in assignments:
                aexpr_vars = expr_vars(aexpr)
                if not aexpr_vars.isdisjoint(e_vars):
                    same.add(aexpr, val, result)
                elif args.verbose_testgen:
                    print 'Ignoring assignment:', (aexpr, val)

            notsame = same.notsame_cond()
            if args.verbose_testgen:
                print 'Negation', self.nmodel, ':', notsame
            e = simsym.symand([e, notsame])

        if self.npathmodel == args.max_tests_per_path:
            print '  Max tests reached for path %s' % result.pathid

        if self.testgen:
            self.testgen.end_path()

    def __on_model(self, result, model):
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
            self.testgen.on_model(smodel)
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
                    help='Methods to run (e.g., stat,fstat)')
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
    if args.check_conds and simsym.check(cond)[0] == z3.unsat:
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

    if args.check_conds and simsym.check(simsym.symnot(c))[0] == z3.unsat:
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
    callsets = []
    if functions is not None:
        calls = []
        for part in functions.split(','):
            if '/' in part:
                callsets.append([getattr(base, fname) for fname in part.split('/')])
            else:
                calls.append(getattr(base, part))
    else:
        calls = [getattr(base, a) for a in dir(base)
                 if hasattr(getattr(base, a), 'model_function_pri')]
        calls.sort(key=lambda x: x.model_function_pri)
    callsets.extend(itertools.combinations_with_replacement(calls, ncomb))
    return callsets

def main(spec_args):
    global args                 # XXX Get rid of this global
    args = spec_args

    z3printer._PP.max_lines = float('inf')
    m = __import__(args.module)
    testgen = m.model_testgen if hasattr(m, 'model_testgen') else None
    if testgen is None and args.test_file:
        parser.error("No test case generator for this module")
    isomorphism_types = getattr(m, 'isomorphism_types', {})

    test_writer = TestWriter(args.trace_file, args.model_file, args.test_file,
                             testgen, isomorphism_types)

    for callset in parse_functions(args.functions, args.ncomb, m):
        do_callset(m.model_class, callset, test_writer)

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
