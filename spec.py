import simsym
import z3
import z3printer
import collections
import itertools
import sys
import argparse
import json
import time

def test(base, *calls):
    all_s = []
    all_r = []

    for callseq in itertools.permutations(range(0, len(calls))):
        s = base()
        r = {}
        seqname = ''.join(map(lambda i: chr(i + ord('a')), callseq))
        for idx in callseq:
            r[idx] = calls[idx](s, chr(idx + ord('a')), seqname)
        all_s.append(s)
        all_r.append(r)

    diverge = ()
    if simsym.symor([all_r[0] != r for r in all_r[1:]]):
        diverge += ('results',)
    if simsym.symor([all_s[0] != s for s in all_s[1:]]):
        diverge += ('state',)

    ## XXX precisely keeping track of what diverges incurs overhead.
    ## Avoid the needless book-keeping for now.
    if len(diverge) == 0: return ()
    return ('something',)

    return diverge

def contains_var(expr):
    if z3.is_var(expr):
        return True
    return any([contains_var(child) for child in expr.children()])

def fnmap(x, fnlist):
    for f in fnlist:
        match = False
        fl = f.as_list()
        for fk, fv in fl[:-1]:
            if fk.eq(x):
                x = fv
                match = True
        if not match:
            x = fl[-1]
    return x

def var_unwrap(e, fnlist, modelctx):
    if not contains_var(e):
        return None
    if z3.is_var(e) and z3.get_var_index(e) == 0:
        fn0 = fnlist[0].as_list()
        retlist = []
        for fkey, fval in fn0[:-1]:
            retlist.append([fkey, fnmap(fval, fnlist[1:])])
        retlist.append(fnmap(fn0[-1], fnlist[1:]))
        return retlist
    if e.num_args() != 1:
        raise Exception('cannot var_unwrap: %s' % str(e))
    arg = e.arg(0)
    f = e.decl()
    return var_unwrap(arg, [modelctx[f]] + fnlist, modelctx)

def model_unwrap(e, modelctx):
    if e is None:
        return None
    if isinstance(e, z3.FuncDeclRef):
        return e.name()
    if isinstance(e, z3.IntNumRef):
        return int(e.as_long())
    if isinstance(e, z3.FuncInterp):
        elist = e.as_list()
        ## Sometimes Z3 gives us assignments like:
        ##   k!21594 = [else -> k!21594!21599(k!21597(Var(0)))],
        ##   k!21597 = [Fn!val!1 -> Fn!val!1, else -> Fn!val!0],
        ##   k!21594!21599 = [Fn!val!0 -> True, else -> False],
        ## Check if elist[0] contains a Var() thing; if so, unwrap the Var.
        if len(elist) == 1:
            var_elist = var_unwrap(elist[0], [], modelctx)
            if var_elist is not None:
                elist = var_elist
        return [model_unwrap(x, modelctx) for x in elist]
    if isinstance(e, z3.BoolRef):
        if z3.is_true(e):
            return True
        if z3.is_false(e):
            return False
        raise Exception('Suspect boolean: %s' % e)
    if isinstance(e, list):
        return [model_unwrap(x, modelctx) for x in e]
    if isinstance(e, z3.ExprRef) and e.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
        univ = modelctx.get_universe(e.sort())
        if univ is None: univ = []
        positions = [i for i, v in enumerate(univ) if v.eq(e)]
        if len(positions) != 1:
            raise Exception('could not find %s in %s' % (str(e), str(univ)))
        return positions[0]
    if isinstance(e, z3.DatatypeRef):
        nc = None
        for i in range(0, e.sort().num_constructors()):
            if e.decl().eq(e.sort().constructor(i)): nc = i
        if nc is None:
            raise Exception('Could not find constructor for %s' % e)
        dict = {}
        for i in range(0, e.sort().constructor(nc).arity()):
            fieldname = str(e.sort().accessor(nc, i))
            dict[fieldname] = model_unwrap(e.arg(i), modelctx)
        return dict
    if isinstance(e, z3.ArrayRef):
        if z3.is_as_array(e):
            f = z3.get_as_array_func(e)
            return model_unwrap(modelctx[f], modelctx)
    raise Exception('%s: unknown type %s' % (e, simsym.strtype(e)))

class IsomorphicMatch(object):
    ## Originally based on http://stackoverflow.com/questions/11867611

    ## We need to construct a condition for two assignments being isomorphic
    ## to each other.  This is interesting for uninterpreted sorts, where
    ## we don't care about the specific value assignment from Z3, and care
    ## only about whether the equality pattern looks the same.  This is
    ## made more complicated by the fact that uninterpreted sorts show up
    ## all over the place: as values of a variable, as values in an array,
    ## as keys in an array, as default 'else' values in an array, etc.

    ## XXX handling FDs and timestamps might be better done by treating
    ## them as supporting order, rather than supporting just equality;
    ## the isomorphism condition would be the values being in the same
    ## order, rather than in the same equality pattern.

    def __init__(self, model):
        self.uninterps = collections.defaultdict(list)
        self.conds = [z3.BoolVal(True)]

        # Try to reach a fixed-point with expressions of uninterpreted
        # sorts used in array indexes.
        self.groups_changed = True
        while self.groups_changed:
            self.groups_changed = False
            self.process_model(model)

        self.process_uninterp()

    def process_model(self, model):
        for decl in model:
            ## Do not bother including "internal" variables in the wrapped model;
            ## otherwise Z3 can iterate over different assignments to these
            ## variables, while we care only about assignments to "external"
            ## variables.
            if '!' in str(decl) or 'internal_' in str(decl) or 'dummy_' in str(decl):
                continue
            self.process_decl_assignment(decl, model[decl], model)

    def process_decl_assignment(self, decl, val, model):
        """Process a single assignment in a model.

        decl must be a z3.FuncDeclRef assigned to z3.ExprRef val in
        the given model.
        """

        if decl.arity() > 0:
            raise Exception('handle nonzero arity')

            ## Handle FuncDeclRef objects -- XXX old code.
            assert(decl.arity() == 1)

            val_list = val.as_list()
            for valarg, valval in val_list[:-1]:
                self.add_equal(decl(self.uwrap(valarg)), valval)

            domain_sorts = [decl.domain(i) for i in range(0, decl.arity())]
            domain_anon = [z3.Const(simsym.anon_name(), s) for s in domain_sorts]
            elsecond = z3.ForAll(domain_anon,
                          z3.Or([decl(*domain_anon) == self.uwrap(val_list[-1])] +
                                [domain_anon[0] == self.uwrap(x)
                                 for x, _ in val_list[:-1]]))
            self.conds.append(elsecond)
            return

        # Calling a FuncDeclRef returns the Z3 function application
        # expression (which, since we weeded out non-zero arity above,
        # will be just the constant being bound by the model,
        # satisfying is_app and is_const).
        dconst = decl()

        symtype = simsym.symbolic_type(dconst)
        self.process_const_assignment(dconst, val, symtype, model)

    def process_const_assignment(self, dconst, val, symtype, model):
        """Process a single constant assignment in model.

        dconst is a projected constant expression, which is either a
        Z3 constant expression, a projection of a projected constant
        expression, or a select of a projected constant expression.
        val is the assignment of dconst in model.  The sort of dconst
        must agree with the type of val (for primitive sorts, they are
        equal; for array sorts, val must be a FuncInterp).  symtype is
        the pseudo-Symbolic type of dconst, as defined by
        simsym.symbolic_type.

        Effectively, this starts with the assignment (dconst == val)
        and recursively decomposes compound values on both sides until
        both dconst and val are primitive sorts.  At this point it
        calls add_assignment to register the primitive assignment.
        """

        dsort = dconst.sort()

        if dsort.kind() == z3.Z3_DATATYPE_SORT:
            raise Exception("Z3_DATATYPE_SORT in process_const_assignment")
            # XXX Should be unused now.  If we do still need this, we
            # need to flow symtype through below.
            nc = None
            for i in range(0, dsort.num_constructors()):
                if val.decl().eq(dsort.constructor(i)): nc = i
            if nc is None:
                raise Exception('Could not find constructor for %s' % str(dconst))
            for i in range(0, dsort.constructor(nc).arity()):
                dconst_field = dsort.accessor(nc, i)(dconst)
                childval = val.children()[i]
                self.process_const_assignment(dconst_field, childval, model)
            return

        if dsort.kind() in [z3.Z3_INT_SORT,
                            z3.Z3_BOOL_SORT,
                            z3.Z3_UNINTERPRETED_SORT]:
            if not z3.is_const(val):
                print 'WARNING: Not a constant:', val
            assert issubclass(symtype, simsym.Symbolic)
            self.add_assignment(dconst, val, symtype)
            return

        if dsort.kind() == z3.Z3_ARRAY_SORT:
            if z3.is_as_array(val):
                func_interp = model[z3.get_as_array_func(val)]
            else:
                func_interp = val
            assert(isinstance(func_interp, z3.FuncInterp))

            flist = func_interp.as_list()

            assert isinstance(symtype, tuple)

            ## Handle Var() things; see comment in model_unwrap().
            if len(flist) == 1:
                var_flist = var_unwrap(flist[0], [], model)
                if var_flist is not None:
                    flist = var_flist

            ## Handle everything except the "else" value
            for fidx, fval in flist[:-1]:
                fidxrep = self.uninterp_representative(fidx)
                if fidxrep is None: continue
                self.process_const_assignment(
                    dconst[fidxrep], fval, symtype[1], model)

            ## One problem is what to do with ArrayRef assignments (in the form of
            ## a FuncInterp), because FuncInterp assigns a value for every index,
            ## but we only care about specific indexes.  (It's not useful to receive
            ## another model that differs only in some index we never cared about.)
            ## To deal with this problem, we add FuncInterp constraints only for
            ## indexes that are interesting.  For uninterpreted sorts, this
            ## is the universe of values for that sort.  For interpreted sorts
            ## (integers), we add constraints for values explicitly listed in
            ## the FuncInterp, and skip the "else" clause altogether.  This is
            ## imprecise: it means self.conds is less constrained than it should
            ## be, so its negation is too strict, and might preclude some
            ## otherwise-interesting assignments.

            if dconst.domain().kind() == z3.Z3_UNINTERPRETED_SORT:
                univ = model.get_universe(dconst.domain())
                if univ is None: univ = []
                for idx in univ:
                    if any([idx.eq(i) for i, _ in flist[:-1]]): continue
                    idxrep = self.uninterp_representative(idx)
                    if idxrep is None: continue
                    self.process_const_assignment(
                        dconst[idxrep], flist[-1], symtype[1], model)
            return

        print dsort.kind()
        raise Exception('handle %s = %s' % (dconst, val))

    def uninterp_groups(self, sort):
        groups = []
        for expr, val in self.uninterps[sort]:
            found = False
            for group_val, group_exprs in groups:
                if val.eq(group_val):
                    group_exprs.append(expr)
                    found = True
            if not found:
                groups.append((val, [expr]))
        return groups

    def uninterp_representative(self, val):
        for expr2, val2 in self.uninterps[val.sort()]:
            if val.eq(val2):
                return expr2
        return None

    def add_assignment(self, expr, val, symtype):
        pseudo_sort = isomorphism_types.get(symtype)
        if pseudo_sort == "ignore":
            return

        sort = val.sort()
        if sort.kind() == z3.Z3_UNINTERPRETED_SORT or pseudo_sort == "equal":
            self.add_assignment_uninterp(expr, val, sort)
            return

        if expr.sort().kind() != z3.Z3_BOOL_SORT:
            print 'WARNING: Interpreted sort assignment:', expr, val

        cond = (expr == val)
        if not any([c.eq(cond) for c in self.conds]):
            self.conds.append(cond)

    def add_assignment_uninterp(self, expr, val, sort):
        new_group = True
        for uexpr, uval in self.uninterps[sort]:
            if uval.eq(val):
                new_group = False
                if uexpr.eq(expr): return
        if new_group:
            self.groups_changed = True
        self.uninterps[sort].append((expr, val))

    def process_uninterp(self):
        for sort in self.uninterps:
            groups = self.uninterp_groups(sort)
            for _, exprs in groups:
                for otherexpr in exprs[1:]:
                    self.conds.append(exprs[0] == otherexpr)
            representatives = [exprs[0] for _, exprs in groups]
            if len(representatives) > 1:
                self.conds.append(z3.Distinct(representatives))

    def notsame_cond(self):
        return simsym.wrap(z3.Not(z3.And(self.conds)))

parser = argparse.ArgumentParser()
parser.add_argument('-c', '--check-conds', action='store_true',
                    help='Check commutativity conditions for sat/unsat')
parser.add_argument('-p', '--print-conds', action='store_true',
                    help='Print commutativity conditions')
parser.add_argument('-m', '--model-file',
                    help='Z3 model output file')
parser.add_argument('-t', '--test-file',
                    help='JSON output file')
parser.add_argument('-n', '--ncomb', type=int, default=2, action='store',
                    help='Number of system calls to combine per test')
parser.add_argument('-f', '--functions', action='store',
                    help='Methods to run (e.g., stat,fstat)')
parser.add_argument('--simplify-more', default=False, action='store_true',
                    help='Use ctx-solver-simplify')
parser.add_argument('--max-testcases', type=int, default=sys.maxint, action='store',
                    help='Maximum # test cases to generate per combination')
parser.add_argument('--verbose-testgen', default=False, action='store_true',
                    help='Print diagnostics during model enumeration')
parser.add_argument('module', metavar='MODULE', default='fs', action='store',
                    help='Module to test (e.g., fs)')
args = parser.parse_args()

if args.model_file is None:
    modelfile = None
else:
    modelfile = open(args.model_file, 'w')

if args.test_file is None:
    testfile = None
else:
    testfile = open(args.test_file, 'w')

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

z3printer._PP.max_lines = float('inf')
m = __import__(args.module)
base = m.model_class

isomorphism_types = getattr(m, 'isomorphism_types', {})

if args.functions is not None:
    calls = [getattr(base, fname) for fname in args.functions.split(',')]
else:
    calls = m.model_functions

testcases = []

for callset in itertools.combinations_with_replacement(calls, args.ncomb):
    print ' '.join([c.__name__ for c in callset])
    conds = collections.defaultdict(lambda: [simsym.wrap(z3.BoolVal(False))])
    for result, condlist in simsym.symbolic_apply(test, base, *callset).items():
        conds[result] = condlist

    # Internal variables help deal with situations where, for the same
    # assignment of initial state + external inputs, two operations both
    # can commute and can diverge (depending on internal choice, like the
    # inode number for file creation).
    commute = simsym.symor(conds[()])
    cannot_commute = simsym.symnot(simsym.exists(simsym.internals(), commute))

    for diverge, condlist in sorted(conds.items()):
        if diverge == ():
            print_cond('can commute', simsym.symor(condlist))
        else:
            print_cond('cannot commute, %s can diverge' % ', '.join(diverge),
                       simsym.symand([simsym.symor(condlist), cannot_commute]))

    if modelfile is not None or testfile is not None:
        if modelfile:
            print >> modelfile, "=== Models for %s ===" % \
                " ".join(c.__name__ for c in callset)
            print >> modelfile

        ncond = 0
        for pathi, e in enumerate(conds[()]):
            if modelfile:
                print >> modelfile, "== Path %d ==" % pathi
                print >> modelfile

            ## This can potentially reduce the number of test cases
            ## by, e.g., eliminating irrelevant variables from e.
            ## The effect doesn't seem significant: one version of Fs
            ## produces 3204 test cases without simplify, and 3182 with.
            e = simsym.simplify(e)
            while ncond < args.max_testcases:
                check, model = simsym.check(e)
                if check == z3.unsat: break
                if check == z3.unknown:
                    # raise Exception('Cannot enumerate: %s' % str(e))
                    print 'Cannot enumerate, moving on..'
                    print 'Failure reason:', model
                    break

                if modelfile:
                    print >> modelfile, model.sexpr()
                    print >> modelfile
                    modelfile.flush()

                ## What should we do about variables that do not show up
                ## in the assignment (e.g., because they were eliminated
                ## due to combining multiple paths)?  One possibility, to
                ## generate more test cases, is to pick some default value
                ## for them (since the exact value does not matter).  Doing
                ## so will force this loop to iterate over all possible
                ## assignments, even to these "missing" variables.  Another
                ## possibility is to extract "interesting" variables from
                ## the raw symbolic expression returned by symbolic_apply().

                if testfile:
                    vars = { model_unwrap(k, model):
                             model_unwrap(model[k], model)
                             for k in model
                             if '!' not in model_unwrap(k, model) }
                    if args.verbose_testgen:
                        print 'New assignment', ncond, ':', vars
                    testcases.append({
                        'calls': [c.__name__ for c in callset],
                        'vars':  vars,
                    })

                ncond += 1
                same = IsomorphicMatch(model)
                notsame = same.notsame_cond()
                if args.verbose_testgen:
                    print 'Negation', ncond, ':', notsame
                e = simsym.symand([e, notsame])
        print '  %d testcases' % ncond

if testfile is not None:
    ## Timestamp keeps track of generated test cases (a poor nonce)
    x = { '__gen_ts': int(time.time()), base.__name__: testcases }
    testfile.write(json.dumps(x, indent=2))
