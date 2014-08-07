import simsym, z3

def reduce_array_ext(expr):
    """Find a subset of expr that still produces array-ext in models.

    This is for producing minimal test cases for a specific class of
    bugs where Z3 exposes the internal array-ext function (e.g., Z3
    issue #125).
    """

    subs = expr.children()
    i = 0
    while i < len(subs):
        nsubs = subs[:i] + subs[i+1:]
        e2 = z3.And(nsubs)
        print subs[i].sexpr(),
        for rep in range(100):
            check = simsym.check(e2)
            if check.is_unknown:
                continue
            if 'array-ext' in check.z3_model.sexpr():
                # Got an array-ext, so subs[i] must not be necessary
                print "=> dropping"
                subs = nsubs
                break
        else:
            # Never got an array-ext, so subs[i] is probably necessary
            print "=> keeping"
            i += 1
    return z3.And(subs)

def dump(expr):
    """Print Python code (or something close) for expr.

    In particular, this prints all of the necessary variable
    declarations.
    """

    have = set()
    def sort_ctor(sort):
        if sort.kind() in (z3.Z3_BOOL_SORT, z3.Z3_INT_SORT, z3.Z3_REAL_SORT):
            return sort.name() + 'Sort()'
        if sort.kind() == z3.Z3_ARRAY_SORT:
            return 'ArraySort(%s, %s)' % (sort_ctor(sort.domain()),
                                          sort_ctor(sort.range()))
        if sort.kind() == z3.Z3_UNINTERPRETED_SORT:
            return 'DeclareSort(%r)' % sort.name()
        raise NotImplementedError('Unimplemented sort %s' % sort)

    def mkvar(name, sort):
        if name not in have:
            have.add(name)
            print '%s = Const(%r, %s)' % (name, name, sort_ctor(sort))

    def rec(e):
        if isinstance(e, z3.QuantifierRef):
            for n in range(e.num_vars()):
                mkvar(e.var_name(n), e.var_sort(n))
        elif z3.is_algebraic_value(e) or \
             z3.is_bv_value(e) or \
             z3.is_int_value(e) or \
             z3.is_rational_value(e):
            pass
        elif z3.is_const(e):
            mkvar(str(e), e.sort())

        for sub in e.children():
            rec(sub)
    rec(expr)
    print expr
