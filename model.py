import simsym

def methodwrap(**kwargs):
    def decorator(m):
        def wrapped(self, whichcall, whichseq):
            args = {}
            for arg in kwargs:
                name = '%s.%s.%s' % (whichcall, m.__name__, arg)
                if arg.startswith('internal_'):
                    name += '.%s' % whichseq
                args[arg] = kwargs[arg].any(name)
                if arg.startswith('internal_'):
                    simsym.add_internal(args[arg])
            return m(self, **args)
        wrapped.__name__ = m.__name__
        return wrapped
    return decorator

class Struct(object):
    __slots__ = []

    def __eq__(self, o):
        if self.__class__ != o.__class__:
            return NotImplemented
        fieldeqs = [getattr(self, field) == getattr(o, field)
                    for field in self.__slots__]
        return simsym.symand(fieldeqs)

    def __ne__(self, o):
        r = (self == o)
        if r is NotImplemented:
            return NotImplemented
        return simsym.symnot(r)

