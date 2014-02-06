"""Test the SIM-commutativity of sets of methods."""

__all__ = ['TestResult', 'Divergence', 'ExecutionMonitorBase', 'test_callset']

import simsym
import z3
import collections
import progress
import model

def callseq_name(callseq):
    """Convert a callseq to a string.

    A callseq is a list or tuple of 0-based indexes into a callset
    giving a sequence of calls.
    """
    return ''.join(chr(idx + ord('a')) for idx in callseq)

class TestResult(collections.namedtuple(
        'TestResult', 'diverge results op_states')):
    """The result of a single SIM commutativity test.

    diverge will be an empty list if the calls under test SIM-commute.
    Otherwise, it will be a non-empty list of Divergence objects
    giving the reason for non-commutativity.  (Currently, this list
    always contains just one divergence because the commutativity test
    aborts as soon as it finds a divergence, but there's no reason it
    couldn't keep going.)

    results will be a list of return values for each method in the
    call set.  This records only the result of one call for each
    method, even though each method may be called multiple times.  If
    the calls are SIM-commutative, then all invocations of a given
    method return the same result anyway.
    """

    def __str__(self):
        return str(self.diverge) + ' ' + str(self.results)

class Divergence(collections.namedtuple('Divergence', 'typ seq1 seq2')):
    """A divergence (or non-commuativity).

    typ is either 'state' or 'result' indicating whether this is a
    divergence in system state or in return values.  seq1 and seq2 are
    the two diverging call sequences.  For a state divergence, seq1
    and seq2 will be permutations of each other.  For a result
    divergence, seq1 and seq2 will end in the same call.
    """

    def __str__(self):
        return '%s/%s %s' % (callseq_name(self.seq1), callseq_name(self.seq2),
                             self.typ)

def test(base, *calls):
    """Test for SIM commutativity of calls

    base must be a class type for the system state.  calls must be the
    unbound methods of base to test for SIM commutativity.  Returns a
    TestResult.  This function must be executed symbolically.
    """

    # Create arguments for each call.  We reuse these arguments in
    # each permutation, so each call receives the same arguments each
    # time we test it.
    args = []
    for callidx, call in enumerate(calls):
        arg_name = '%s.%s' % (callseq_name([callidx]), call.__name__)
        args.append(call.arg_struct_type.var(arg_name))

    # op_states[op_index] is a list of pairs of before and after
    # states for operation op_index.
    op_states = [[] for _ in calls]

    # Mapping from frozenset of call indexes to a pair of (callseq,
    # state after callseq).  Prepare with initial state.
    init = base.var(base.__name__)
    perm_states = {frozenset([]): ([], init)}

    # Mapping from callidx to pair of (callseq ending in callidx,
    # result of last call in callseq).
    call_results = {}

    # List of Divergences
    diverge = []

    # Explore every permutation of calls, requiring that the state
    # following every permutation of every subset of callseq be the
    # same.  This uses a depth-first walk of every n-step path from
    # one corner to the opposite corner of an n-dimensional cube,
    # where n is the number of calls.  Each edge represents a call
    # (the edge's direction determines which call) and each vertex a
    # state.  Where these paths rejoin, the states must be equal.
    # This way, we make the minimal number of calls and state
    # comparisons possible.
    def rec(callseq):
        base_state = perm_states[frozenset(callseq)][1]

        # Extend callseq in every way that doesn't duplicate a call
        # already in callseq
        for callidx in range(len(calls)):
            if callidx in callseq:
                continue
            if diverge:
                return
            ncallseq = callseq + (callidx,)
            seqname = callseq_name(callseq)
            # Include the sequence in all anonymous variable names
            simsym.anon_info = '_seq' + seqname
            # Record our call sequence as a schedule note
            simsym.note(('begin', ncallseq))

            # Build the Python arguments dictionary and copy each
            # argument, just in case the call mutates it
            arg_struct = args[callidx]
            cargs = {arg: getattr(arg_struct, arg).copy()
                     for arg in arg_struct._fields}
            # Invoke the call
            nstate = base_state.copy()
            model.cur_thread_idx = callidx
            try:
                res = calls[callidx](nstate, **cargs)
            finally:
                model.cur_thread_idx = None
                simsym.note(('end', ncallseq, res))

            # Record or check result
            call_result = call_results.get(callidx)
            if call_result is None:
                # This is the first time we've made this call.  Record
                # its result.
                call_results[callidx] = (ncallseq, res)
            else:
                # We've called this call before.  Check that its
                # result agrees.
                if call_result[1] != res:
                    diverge.append(
                        Divergence('result', call_result[0], ncallseq))
            if diverge:
                return

            # Record or check state
            op_states[callidx].append((base_state, nstate))
            perm_state = perm_states.get(frozenset(ncallseq))
            if perm_state is None:
                # This is the first permutation of these calls we've
                # executed.  Record the state and recurse.
                perm_states[frozenset(ncallseq)] = (ncallseq, nstate)
                rec(ncallseq)
            else:
                # We've executed some other permutation of these calls
                # already.  Check that the state agrees.  Recursing
                # from here would be redundant.
                if perm_state[1] != nstate:
                    diverge.append(Divergence('state', perm_state[0], ncallseq))
    try:
        rec(())
    finally:
        simsym.anon_info = ''

    return TestResult(diverge,
                      [call_results[callidx][1]
                       for callidx in range(len(calls))],
                      op_states)

class ExecutionMonitorBase(object):
    """Base class for model execution monitoring."""

    def get_progress_format(self):
        """Return a format string for progress reporting this monitor.

        The format string should use "{0}" to refer to this object.
        """
        return None

    def begin_call_set(self, callset):
        """Handle the beginning of a call set.

        callset is a list of method objects representing the methods
        being tested for commutativity.

        For this call set, the model executor will generate a set of
        code paths with disjoint path constraints and symbolic
        results.  For each of these, it will call on_path.  When it
        completes all paths in this call set, it will call
        end_call_set.
        """
        pass

    def stop_call_set(self):
        """Return True if path enumeration should stop for this call set."""
        return False

    def on_path(self, result):
        """Handle the completion of a call path.

        result is the simsym.SymbolicApplyResult representing this
        code path and its final result.  result.value will be a
        TestResult giving the result of the SIM commutativity test.
        """
        pass

    def end_call_set(self):
        """Handle the end of a call set."""
        pass

    def finish(self):
        """Finish test generation.

        This will be called after all call sets.  The model executor
        will invoke no further methods after this call.

        The default implementation of this method does nothing.
        """
        pass

class StatMonitor(ExecutionMonitorBase):
    def __init__(self):
        super(StatMonitor, self).__init__()
        self.npath = self.ncompath = 0

    def get_progress_format(self):
        return '{0.npath} paths ({0.ncompath} commutative)'

    def on_path(self, result):
        super(StatMonitor, self).on_path(result)
        self.npath += 1
        if len(result.value.diverge) == 0:
            self.ncompath += 1

class MetaMonitor(ExecutionMonitorBase):
    def __init__(self, monitors):
        self._monitors = monitors

    def get_progress_format(self):
        sub = [m.get_progress_format() for m in self._monitors]
        return ', '.join(fmt.replace('{0.', '{0._monitors[%d].' % i)
                         for i, fmt in enumerate(sub) if fmt)

    def begin_call_set(self, callset):
        for m in self._monitors:
            m.begin_call_set(callset)

    def stop_call_set(self):
        return any(m.stop_call_set() for m in self._monitors)

    def on_path(self, result):
        for m in self._monitors:
            m.on_path(result)

    def end_call_set(self):
        for m in self._monitors:
            m.end_call_set()

    def finish(self):
        for m in self._monitors:
            m.finish()

def print_cond(msg, cond, check_conds, print_conds):
    if check_conds and simsym.check(cond).is_unsat:
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

    if check_conds and simsym.check(simsym.symnot(c)).is_unsat:
        s = 'always'
    else:
        if print_conds:
            scond = simsym.simplify(cond, print_conds == 'simplify')
            s = '\n    ' + str(scond).replace('\n', '\n    ')
        else:
            if check_conds:
                s = 'sometimes'
            else:
                s = 'maybe'
    print '  %s: %s' % (msg, s)

def test_callset(base, callset, monitors,
                 check_conds=False, print_conds=False):
    """Test the SIM-commutativity of a call set.

    base must be a class type for the system state.  calls must be the
    unbound methods of base to test for SIM commutativity.  As the
    test proceeds, this will invoke the appropriate methods of the
    ExecutionMonitorBase instances in monitors.  The caller is
    responsible for calling the 'finish' method of the monitors after
    all callsets are done.

    If check_conds is true, check commutativity conditions for
    sat/unsat and report this.  If print_conds is true, print
    commutativity conditions.  If print_conds is "simplify", use
    ctx-solver-simplify to further simplify conditions.
    """

    monitor = MetaMonitor([StatMonitor()] + monitors)

    print ' '.join([c.__name__ for c in callset])
    monitor.begin_call_set(callset)
    
    reporter = progress.ProgressReporter(
        '  ' + monitor.get_progress_format(), monitor)

    condlists = collections.defaultdict(list)
    terminated = False
    diverged = set()
    all_internals = []
    for sar in simsym.symbolic_apply(test, base, *callset):
        if sar.type == 'value':
            is_commutative = (len(sar.value.diverge) == 0)
            diverged.update(sar.value.diverge)
            condlists[is_commutative].append(sar.path_condition)
            all_internals.extend(sar.internals)
        monitor.on_path(sar)
        if monitor.stop_call_set():
            terminated = True
            break

    monitor.end_call_set()
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
        print_cond('can commute', commute, check_conds, print_conds)
    else:
        cannot_commute = True

    if False in condlists:
        diverge = simsym.symor(condlists[False])
        print_cond('can not commute; %s' % ', '.join(map(str, diverged)),
                   simsym.symand([diverge, cannot_commute]),
                   check_conds, print_conds)
