import z3
from simsym import *

class SListBase(Symbolic):
    def init_assumptions(self):
        return self._len >= 0

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

def tlist(valueType, lenType=SInt):
    """Return a new list type whose values are valueType.

    lenType, if specified, will be the type used for indexes and
    length.  It must be an ordered type and support '+' (which
    effectively means it has to be SInt or a synonym type).
    """

    name = "SList_" + valueType.__name__
    base = tstruct(_vals = tmap(lenType, valueType), _len = lenType)
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

class SBagBase(Symbolic):
    def add(self, val):
        assume(self._imap[val] >= 0)
        self._imap[val] = self._imap[val] + 1

    def take(self):
        v = self._valueType.any()
        add_internal(v)
        assume(self._imap[v] > 0)
        self._imap[v] = self._imap[v] - 1
        return v

def tbag(valueType):
    name = "SBag_" + valueType.__name__
    mapType = tmap(valueType, SInt)
    base = tstruct(_imap = mapType)
    return type(name, (base, SBagBase), {"_valueType": valueType})

