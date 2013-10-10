"""LINQ-like enumerables"""

import collections
import itertools
import operator

__all__ = "Grouping Enumerable".split()

Grouping = collections.namedtuple('Grouping', 'key values')

class Enumerable(object):
    def __init__(self, genfn, *args):
        self.__genfn = genfn
        self.__args = args

    @classmethod
    def from_iterable(cls, iterable):
        return cls(iter, iterable)

    def __iter__(self):
        return self.__genfn(*self.__args)

    def __len__(self):
        l = 0
        for _ in self:
            l += 1
        return l

    def __fn(self, fn):
        if callable(fn):
            return fn
        return eval('lambda _: ' + fn, {})

    def select(self, fn):
        fn = self.__fn(fn)
        return type(self)(itertools.imap, fn, self)

    def where(self, pred):
        pred = self.__fn(pred)
        return type(self)(itertools.ifilter, pred, self)

    def group_by(self, key_selector, elem_fn=None, aggr_fn=None):
        key_selector = self.__fn(key_selector)
        elem_fn = None if elem_fn is None else self.__fn(elem_fn)
        aggr_fn = Grouping if aggr_fn is None else self.__fn(aggr_fn)

        def group_by_gen():
            groups = collections.OrderedDict()
            for elem in self:
                key = key_selector(elem)
                group = groups.get(key)
                if group is None:
                    groups[key] = group = []
                if elem_fn:
                    group.append(elem_fn(elem))
                else:
                    group.append(elem)

            while groups:
                key, elems = groups.popitem(last=False)
                yield aggr_fn(key, type(self).from_iterable(elems))
        return Enumerable(group_by_gen)

    def concat(self, *others):
        return type(self)(itertools.chain, self, *others)

    def join(self, inner, outer_key_selector, inner_key_selector,
             result_fn):
        outer_key_selector = self.__fn(outer_key_selector)
        inner_key_selector = self.__fn(inner_key_selector)
        result_fn = self.__fn(result_fn)

        def join_gen():
            # Index inner
            inner_idx = collections.defaultdict(list)
            for irec in inner:
                inner_idx[inner_key_selector(irec)].append(irec)

            # Scan outer
            for orec in self:
                irecs = inner_idx.get(outer_key_selector(orec), None)
                if irecs:
                    for irec in irecs:
                        yield result_fn(orec, irec)
        return type(self)(join_gen)

    def str_table(self, fields_fns=None, max_width=20):
        if fields_fns is None:
            try:
                row = iter(self).next()
            except StopIteration:
                return ''
            if not hasattr(row, '_fields'):
                fields_fns = [('str(_)', str)]
            else:
                fields_fns = [(field, operator.attrgetter(field))
                              for field in row._fields]
        else:
            fields_fns = [(name, self.__fn(fn)) for name, fn in fields_fns]

        def trim(obj):
            s = str(obj)
            if len(s) > max_width:
                return s[:max_width - 3] + '...'
            return s
        strs = [[name for name, _ in fields_fns]] + \
               [[trim(fn(row)) for name, fn in fields_fns] for row in self]
        widths = [0] * len(fields_fns)
        for row in strs:
            for i, s in enumerate(row):
                widths[i] = max(widths[i], len(s))
        for i, row in enumerate(strs):
            strs[i] = ' '.join(s.ljust(w) for s, w in zip(row, widths))
        return '\n'.join(strs)
