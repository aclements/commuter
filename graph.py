__all__ = ['Graph']

import sys, subprocess, tempfile, collections

def dot_val(obj):
    if isinstance(obj, (int, float, bool)):
        return str(obj)
    if isinstance(obj, unicode):
        obj = obj.encode('utf-8')
    if isinstance(obj, str):
        if obj.isalnum() and obj[0].isalpha():
            return obj
        return '"' + (obj.replace('\\', '\\\\')
                      .replace('\n', '\\l')
                      .replace('"', '\\"')) + '"'
    raise TypeError("Don't know how to convert %r to dot" % (obj,))

def dot_attrs(attrs):
    return '[%s]' % ','.join('%s=%s' % (k, dot_val(v)) for k, v in attrs.items()
                             if v is not None)

class GNode(object):
    def __init__(self, obj, unique=False, **attrs):
        self.__obj = obj
        self.__unique = unique
        self.__attrs = tuple(attrs.iteritems())

    def __hash__(self):
        if self.__unique:
            return super(GNode, self).__hash__()
        return hash((self.__obj, self.__attrs))

    def __eq__(self, o):
        if self.__unique or o.__unique:
            return self is o
        return self.__obj == o.__obj and self.__attrs == o.__attrs

    def _to_dot(self, graph, nid):
        attrs = dict(self.__attrs)
        attrs.update(graph.obj_attrs(self.__obj))
        return '%s %s;' % (dot_val(nid), dot_attrs(attrs))

class Graph(object):
    def __init__(self):
        self.__graph_attrs = {}
        self.__node_attrs = {}
        self.__edge_attrs = {}
        # Use an ordered dict to keep the nodes in order
        self.__nodes = collections.OrderedDict()
        self.__edges = set()

    def graph_attrs(self, **attrs):
        self.__graph_attrs.update(attrs)
        return self

    def node_attrs(self, **attrs):
        self.__node_attrs.update(attrs)
        return self

    def edge_attrs(self, **attrs):
        self.__edge_attrs.update(attrs)
        return self

    def node(self, obj, unique=False, **attrs):
        node = GNode(obj, unique, **attrs)
        self.__nodes[node] = True
        return node

    def edge(self, n1, n2, **attrs):
        self.__edges.add((n1, n2, tuple(attrs.iteritems())))

    def show(self):
        try:
            with tempfile.NamedTemporaryFile(suffix=".pdf") as f:
                p = subprocess.Popen(["dot", "-Tpdf"], stdin=subprocess.PIPE,
                                     stdout=f)
                self.to_dot(p.stdin)
                p.stdin.close()
                p.wait()
                subprocess.check_call(["evince", f.name])
        except Exception as e:
            print >> sys.stderr, "Suppressing exception from Graph.show():"
            import traceback; traceback.print_exc()

    def to_dot(self, fp=sys.stdout):
        print >>fp, 'digraph G {'
        for name, attrs in [('graph', self.__graph_attrs),
                            ('node',  self.__node_attrs),
                            ('edge',  self.__edge_attrs)]:
            if attrs:
                print >>fp, '%s %s;' % (name, dot_attrs(attrs))
        nids = {}
        for i, node in enumerate(self.__nodes):
            nids[node] = 'n%d' % i
            print >>fp, node._to_dot(self, nids[node])
        for src, dst, attrs in self.__edges:
            print >>fp, '%s -> %s %s;' % (nids[src], nids[dst],
                                          dot_attrs(dict(attrs)))
        print >>fp, '}'

    def obj_attrs(self, obj):
        return {'label': unicode(obj)}
