import z3
from simsym import *

class SListBase(Symbolic):
    @classmethod
    def var(cls, *args, **kwargs):
        return super(SListBase, cls).var(*args, _start=0, **kwargs)

    def _declare_assumptions(self, assume):
        super(SListBase, self)._declare_assumptions(assume)
        assume(self._len >= 0)

    def __check_idx(self, idx):
        if idx < 0:
            raise IndexError("SList index out of range: %r < %r" % (idx, 0))
        if idx >= self.len():
            raise IndexError("SList index out of range: %r >= %r" %
                             (idx, self._len))
        return idx

    def __getitem__(self, idx):
        return self._vals[self.__check_idx(idx) + self._start]

    def __setitem__(self, idx, val):
        self._vals[self.__check_idx(idx) + self._start] = val

    def __eq__(self, o):
        if type(o) != type(self):
            return NotImplemented
        i = SInt.var()
        return symand([self._len == o._len,
                       forall(i, implies(symand([i >= 0, i < self._len]),
                                         self._vals[i + self._start] ==
                                         o._vals[i + o._start]))])

    def len(self):
        # Overriding __len__ isn't useful because the len() builtin
        # will try hard to coerce it to an integer.
        return self._len

    def append(self, val):
        l = self.len()
        self._len += 1
        self[l] = val

    def shift(self, by=1):
        if by == 0:
            return
        self.__check_idx(by - 1)
        self._len -= by
        self._start += by

def tlist(valueType, lenType=SInt):
    """Return a new list type whose values are valueType.

    lenType, if specified, will be the type used for indexes and
    length.  It must be an ordered type and support '+' (which
    effectively means it has to be SInt or a synonym type).
    """

    name = "SList_" + valueType.__name__
    base = tstruct(_vals = tmap(lenType, valueType), _len = lenType,
                   _start = lenType)
    return type(name, (SListBase, base), {})

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

    def __eq__(self, o):
        if type(self) != type(o):
            return NotImplemented
        key = self._map._indexType.var()
        return symand([self._valid == o._valid,
                       forall(key, implies(self._valid[key],
                                           self._map[key] == o._map[key]))])

    @classmethod
    def empty(cls, name=None):
        return cls.var(name, _valid=cls._valid_type.constVal(False))

    def contains(self, key):
        return self._valid[key]

    def __contains__(self, key):
        # The "in" operator will force our result to a boolean, which
        # we don't want.  However, if we don't provide a __contains__,
        # "in" will attempt to iterate over this object by calling
        # __getitem__ for successive integers, which is *really* not
        # what we want.  So complain.
        raise Exception("Use SDictBase.contains instead of the 'in' operator")

    def create(self, key):
        """Return the value at key, creating it if necessary.

        Note that there are no guarantees about the returned value,
        even if it is freshly created (e.g., if a value at this key
        was previously deleted, this will revive that deleted value).
        The caller should be sure to override anything that matters in
        the returned value.
        """

        self._valid[key] = True
        return self._map[key]

def tdict(keyType, valueType):
    name = "SDict_" + keyType.__name__ + "_" + valueType.__name__
    valid_type = tmap(keyType, SBool)
    base = tstruct(_map = tmap(keyType, valueType),
                   _valid = valid_type)
    return type(name, (SDictBase, base), {'_valid_type':valid_type})

class SSetBase(Symbolic):
    @classmethod
    def empty(cls):
        return cls.var(_bmap = cls._mapType.constVal(False))

    @classmethod
    def all(cls):
        return cls.var(_bmap = cls._mapType.constVal(True))

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
        v = self._valueType.var()
        add_internal(v)
        assume(self._imap[v] > 0)
        self._imap[v] = self._imap[v] - 1
        return v

def tbag(valueType):
    name = "SBag_" + valueType.__name__
    mapType = tmap(valueType, SInt)
    base = tstruct(_imap = mapType)
    return type(name, (base, SBagBase), {"_valueType": valueType})

