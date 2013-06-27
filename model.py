import simsym

def methodwrap(**kwargs):
    def decorator(m):
        def wrapped(self, whichcall, whichseq):
            args = {}
            for arg in kwargs:
                name = '%s.%s.%s' % (whichcall, m.__name__, arg)
                if arg.startswith('internal_'):
                    name += '.%s' % whichseq
                args[arg] = kwargs[arg].var(name)
                if arg.startswith('internal_'):
                    simsym.add_internal(args[arg])
            return m(self, **args)
        wrapped.__name__ = m.__name__
        return wrapped
    return decorator
