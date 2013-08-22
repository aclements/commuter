import simsym

priority = 0

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

    For each argument, each call in a call set gets a distinct
    symbolic variable, but that same variable is reused regardless of
    the order the call set is invoked in (hence, the value of the
    argument is fixed across permutations).
    """

    # Create symbolic struct type for the arguments
    arg_struct_type = simsym.tstruct(**arg_types)

    def decorator(m):
        def wrapped(self, whichcall):
            # Create the arguments for this call.  Note that this will
            # construct the same name for the n'th call in the call
            # set, regardless of its current position in the
            # permutation, so we'll get the same initial symbolic
            # value.
            name = "%s.%s" % (whichcall, m.__name__)
            arg_struct = arg_struct_type.var(name)

            # Build Python arguments dictionary
            args = {arg: getattr(arg_struct, arg) for arg in arg_types}

            return m(self, **args)
        wrapped.__name__ = m.__name__
        global priority
        wrapped.model_function_pri = priority
        priority += 1
        return wrapped
    return decorator
