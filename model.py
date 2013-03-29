import simsym

def methodwrap(**kwargs):
    def decorator(m):
        def wrapped(self, which):
            args = { arg: kwargs[arg].any('%s[%s].%s' % (m.__name__, which, arg))
                     for arg in kwargs }
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

