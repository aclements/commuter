import z3
from simsym import *

class SListBase(Symbolic):
    @classmethod
    def any(cls, name):
        obj = super(SListBase, cls).any(name)
        assume(obj._len >= 0)
        return obj

    def __check_idx(self, idx):
        if idx < 0:
            raise IndexError("SList index out of range: %r < %r" % (idx, 0))
        if idx >= self.len():
            raise IndexError("SList index out of range: %r >= %r" %
                             (idx, self._len))
        return idx

    def __getitem__(self, idx):
        return self._vals[self.__check_idx(idx)]

    def __setitem__(self, idx, val):
        self._vals[self.__check_idx(idx)] = val

    def len(self):
        # Overriding __len__ isn't useful because the len() builtin
        # will try hard to coerce it to an integer.
        return self._len

    def append(self, val):
        l = self.len()
        self._len += 1
        self[l] = val

def tlist(valueType):
    name = "SList_" + valueType.__name__
    base = tstruct(_vals = tmap(SInt, valueType), _len = SInt)
    return type(name, (base, SListBase), {})

class SDictBase(Symbolic):
    def __getitem__(self, key):
        if self._valid[key]:
            return self._map[key]
        raise KeyError(key)

    def __setitem__(self, key, val):
        self._valid[key] = True
        self._map[key] = val

    def __delitem__(self, key):
        self._valid[key] = False

    def contains(self, key):
        return self._valid[key]

def tdict(keyType, valueType):
    name = "SDict_" + keyType.__name__ + "_" + valueType.__name__
    base = tstruct(_map = tmap(keyType, valueType),
                   _valid = tmap(keyType, SBool))
    return type(name, (base, SDictBase), {})

class SSetBase(Symbolic):
    @classmethod
    def empty(cls):
        return cls.constVal(_bmap = cls._mapType.constVal(False))

    @classmethod
    def all(cls):
        return cls.constVal(_bmap = cls._mapType.constVal(True))

    def add(self, val):
        self._bmap = self._bmap.store(val, True)

    def clear(self, val):
        self._bmap = self._mapType.constVal(False)

    def discard(self, val):
        self._bmap = self._bmap.store(val, False)

    def contains(self, val):
        return self._bmap[val]

def tset(valueType):
    """Return a set type with the given value type."""
    name = "SSet_" + valueType.__name__
    mapType = tmap(valueType, SBool)
    base = tstruct(_bmap = mapType)
    return type(name, (base, SSetBase), {"_mapType": mapType})

class SBag(object):
    def __init__(self, name):
        self._name_prefix = name
        self._items = []
        self._choices = 0

    def add(self, v):
        self._items.append(v)

    def choose(self):
        self._choices = self._choices + 1
        choicevar = SInt.any('%s.choose.%d' % (self._name_prefix, self._choices))
        add_internal(choicevar)
        for i in range(0, len(self._items)):
            if choicevar == i:
                return self._items[i]

        # The bag also contains arbitrary other items
        newvar = SInt.any('%s.someitem.%d' % (self._name_prefix, self._choices))
        return newvar

    def __eq__(self, o):
        if not isinstance(o, SBag):
            return False

        ol = list(o._items)
        for e1 in self._items:
            found = False
            for e2 in ol:
                if e1 == e2:
                    ol.remove(e2)
                    found = True
                    break
            if not found:
                return False
        return True

    def __ne__(self, o):
        return not self.__eq__(o)
