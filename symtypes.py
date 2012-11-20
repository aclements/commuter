import z3
from simsym import *

class SList(object):
    def __init__(self, name, valSort):
        self._vals = z3.Array(name, z3.IntSort(), valSort)
        self._len = wrap(z3.Int(name + '.len'))
        assume(self._len >= 0)

    def __check_idx(self, idx):
        if idx < 0:
            raise IndexError("SList index out of range: %r < %r" % (idx, 0))
        if idx >= self.len():
            raise IndexError("SList index out of range: %r >= %r" %
                             (idx, self._len))
        return unwrap(idx)

    def __getitem__(self, idx):
        return wrap(self._vals[self.__check_idx(idx)])

    def __setitem__(self, idx, val):
        self._vals = z3.Store(self._vals, self.__check_idx(idx), unwrap(val))

    def __eq__(self, o):
        if not isinstance(o, SList):
            return NotImplemented
        return wrap(z3.And(unwrap(self._len == o._len),
                                 self._vals == o._vals))

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return wrap(z3.Not(unwrap(r)))

    def len(self):
        # Overriding __len__ isn't useful because the len() builtin
        # will try hard to coerce it to an integer.
        return self._len

    def append(self, val):
        l = self.len()
        self._len += 1
        self[l] = val

class SDict(object):
    def __init__(self, name, keySort, valSort):
        self._map = z3.Array(name, keySort, valSort)
        self._valid = z3.Array(name + '.valid', keySort, z3.BoolSort())

    def __getitem__(self, key):
        key = unwrap(key)
        if self._valid[key]:
            return self._map[key]
        raise KeyError(key)

    def __setitem__(self, key, val):
        key, val = unwrap(key), unwrap(val)
        self._valid = z3.Store(self._valid, key, True)
        self._map = z3.Store(self._map, key, val)

    def __eq__(self, o):
        if not isinstance(o, SDict):
            return NotImplemented
        return wrap(z3.And(unwrap(self._valid == o._valid),
                                 unwrap(self._map == o._map)))

    def __ne__(self, o):
        r = self == o
        if r is NotImplemented:
            return NotImplemented
        return wrap(z3.Not(unwrap(r)))

class SBag(object):
    def __init__(self, name):
        self._name_prefix = name
        self._items = []
        self._choices = 0

    def add(self, v):
        self._items.append(v)

    def choose(self):
        self._choices = self._choices + 1
        choicevar = anyInt('%s.choose.%d' % (self._name_prefix, self._choices))
        for i in range(0, len(self._items)):
            if choicevar == i:
                return self._items[i]

        # The bag also contains arbitrary other items
        newvar = anyInt('%s.someitem.%d' % (self._name_prefix, self._choices))
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

def anyListOfInt(name):
    return SList(name, z3.IntSort())

def anyDictOfIntToInt(name):
    return SDict(name, z3.IntSort(), z3.IntSort())
