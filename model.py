import simsym

def methodwrap(**arg_types):
    """Transform a method into a testable model method.

    This returns a decorator for model class methods to make them
    testable.  The keys of arg_types must correspond to the wrapped
    method's arguments (except 'self'), and its values must give the
    symbolic types of those arguments.  The decorated method will take
    a string identifying the call in the call set being tested (which
    must stay the same regardless of permutation).  This method
    invokes the wrapped method with the appropriate symbolic values
    for its arguments.

    This supports two types of arguments: regular and "internal"
    arguments.  For regular arguments, each call in a call set gets a
    distinct symbolic variable, but that same variable is reused
    regardless of the order the call set is invoked in (hence, the
    value of the argument is fixed across permutations).  Internal
    arguments are allowed to differ between the same call in different
    permutations; they represent non-deterministic or "internal"
    choices the method can make.  The name of an internal argument
    must begin with "internal_".
    """

    # Separate regular and "internal" arguments.
    regular, internal = {}, {}
    for name, typ in arg_types.items():
        if name.startswith("internal_"):
            internal[name] = typ
        else:
            regular[name] = typ

    # Create symbolic struct types for the regular arguments and for
    # the internal arguments
    regular_struct = simsym.tstruct(**regular)
    internal_struct = simsym.tstruct(**internal)

    def decorator(m):
        def wrapped(self, whichcall):
            # Create the regular arguments for this call.  Note that
            # this will construct the same name for the n'th call in
            # the call set, regardless of its current position in the
            # permutation, so we'll get the same initial symbolic
            # value.
            name = "%s.%s" % (whichcall, m.__name__)
            regular_args = regular_struct.var(name)
            # Create the internal arguments for this call.  This is
            # given an anonymous name so it can have a different value
            # for each call and every code path.
            internal_args = internal_struct.var('internal_*')

            # Build Python arguments dictionary
            args = {}
            for arg in regular:
                args[arg] = getattr(regular_args, arg)
            for arg in internal:
                args[arg] = getattr(internal_args, arg)

            return m(self, **args)
        wrapped.__name__ = m.__name__
        return wrapped
    return decorator
