import json
import collections
from enum import Enumerable

TestCase = collections.namedtuple('TestCase', 'calls path test shared')

class TestSet(Enumerable):
    """An Enumerable of TestCases."""

    def __str__(self):
        return "%d+%d/%d" % (self.shared, self.nonshared, self.total)

    @property
    def shared(self):
        """The number of shared (conflicted) cases."""
        return len(self.where('_.shared'))

    @property
    def shared_frac(self):
        """The fraction of shared (conflicted) cases."""
        return self.shared / float(self.total)

    @property
    def nonshared(self):
        """The number of non-shared (conflict-free) cases."""
        return len(self) - self.shared

    @property
    def nonshared_frac(self):
        """The fraction of non-shared (conflict-free) cases."""
        return self.nonshared / float(self.total)

    @property
    def total(self):
        """The total number of test cases."""
        return len(self)

    @property
    def calls(self):
        """The list of calls covered by this test case set."""
        return sorted(set(self.select('_.calls.split("_")[0]')))

    def table_ul(self, calls=None):
        """Return an upper-left Table of TestSet relations.

        calls, if provided, is a list of call names to use for the
        rows.  If omitted, it defaults to self.calls.  The column
        labels will be the reverse of this list.  The returned table
        is upper-left triangular and empty cells will be filled with
        None.
        """

        if calls is None:
            calls = self.calls

        rows = [[None] * len(calls) for _ in calls]
        for testcalls, testcases in self.group_by('_.calls'):
            call1, call2 = testcalls.split('_')
            if call1 in calls and call2 in calls:
                i1, i2 = sorted([calls.index(call1), calls.index(call2)])
                rows[i1][-i2-1] = testcases
        return Table(rows, list(reversed(calls)), list(calls))

class Table(object):
    def __init__(self, rows, col_labels, row_labels):
        self.rows, self.col_labels, self.row_labels \
            = rows, col_labels, row_labels

    def __str__(self):
        return self.text()

    def text(self, shade=False):
        """Return this table in text form.

        If shade is true, embed VT100 color codes to darken cells with
        a false value.
        """

        table = [[label] + row
                 for label, row in zip(self.row_labels, self.rows)]
        table = [[''] + self.col_labels] + table

        widths = []
        for row in table:
            if len(row) > len(widths):
                widths.extend([0] * (len(row) - len(widths)))
            for coli, col in enumerate(row):
                if col is not None:
                    widths[coli] = max(widths[coli], len(str(col)))

        lines = []
        for row in table:
            text = ''
            for w, v in zip(widths, row):
                cell = '%*s' % (w, '' if v is None else v)
                if shade and not v:
                    cell = '\033[1;30m' + cell + '\033[0m'
                text += cell + ' '
            lines.append(text)
        return '\n'.join(lines)

    def map(self, fn):
        """Apply fn to the Enumerable in each cell and return a new Table."""
        nrows = [[v if v is None else fn(v)
                   for v in row] for row in self.rows]
        return Table(nrows, self.col_labels, self.row_labels)

    def mapget(self, field):
        """Get the specified field from each cell and return a new Table."""
        return self.map(lambda v: getattr(v, field))

    def get(self, x, y):
        """Get cell x, y from the table, or None."""
        if x < 0 or y < 0 or y >= len(self.rows) or x >= len(self.rows):
            return None
        return self.rows[y][x]

def mscan(fp):
    """Parse an mscan.out into a TestSet."""

    data = json.load(fp)
    cases = []
    for testcase in data['testcases']:
        name = testcase['name'].split('-', 1)[1]
        calls, pathid, testnum = name.rsplit('_', 2)
        cases.append(TestCase(calls=calls, path=calls+'_'+pathid, test=name,
                              shared=testcase['shared']))
    return TestSet.from_iterable(cases)

TestModel = collections.namedtuple(
    'TestModel',
    'calls path test idempotent_projs idempotence_unknown assignments')

def model_tests(fp):
    """Parse a model.out file into an Enumerable of TestModels.

    The returned Enumerable will have one entry per test.  Models that
    did not generate any tests are excluded.
    """

    data = json.load(fp)
    models = []
    for calls, paths in data['tests'].iteritems():
        for pathinfo in paths.itervalues():
            path = pathinfo['id']
            for testinfo in pathinfo.get('tests', []):
                test = testinfo['id']
                models.append(TestModel(
                    calls=calls, path=path, test=test,
                    idempotent_projs=testinfo.get('idempotent_projs', None),
                    idempotence_unknown=testinfo.get('idempotence_unknown', 0),
                    assignments=testinfo['assignments']))
    return Enumerable.from_iterable(models)
