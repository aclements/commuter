import simsym

priority = 0

def methodwrap(**arg_types):
    """Transform a method into a testable model method.

    This returns a decorator for model class methods to make them
    testable.  The keys of arg_types must correspond to the wrapped
    method's arguments (except 'self'), and its values must give the
    symbolic types of those arguments.  The decorator returns the
    function given to it, but augmented with an arg_struct_type
    attribute that gives the symbolic struct for its arguments.
    """

    # Create symbolic struct type for the arguments
    arg_struct_type = simsym.tstruct(**arg_types)

    def decorator(m):
        m.arg_struct_type = arg_struct_type
        global priority
        m.model_function_pri = priority
        priority += 1
        return m
    return decorator
