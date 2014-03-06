"""2D rendering contexts"""

from xml.sax.saxutils import escape, quoteattr

__all__ = "SVG TikZ".split()

class _ContextBase(object):
    def __init__(self):
        # Font size in points
        self.font_size = 10
        self._unwind = []
        self._save = ['font_size', '_unwind']

    def __enter__(self):
        state = {field: getattr(self, field) for field in self._save}
        def restore():
            for k, v in state.iteritems():
                setattr(self, k, v)
        self._unwind = [restore]

    def __exit__(self, *args):
        for unwind in reversed(self._unwind):
            unwind()

    def translate(self, x, y):
        raise NotImplementedError

    def rect(self, x, y, w, h, fill=None, stroke=None, stroke_width=None):
        raise NotImplementedError

    def circle(self, x, y, r, fill=None, stroke=None, stroke_width=None):
        raise NotImplementedError

    def path(self, points, fill=None, stroke=None, stroke_width=None):
        raise NotImplementedError

    def clip(self, points):
        raise NotImplementedError

    def _canonPath(self, points):
        o = []
        lx, ly = 0, 0
        for pt in points:
            if pt == 'Z':
                o.append('Z')
            elif pt[0] == 'M':
                o.append(pt)
                lx, ly = pt[1:]
            else:
                if pt[0] == 'L':
                    px, py = pt[1:]
                elif pt[0] == 'l':
                    px, py = lx + pt[1], ly + pt[2]
                elif pt[0] == 'H':
                    px, py = pt[1], ly
                elif pt[0] == 'V':
                    px, py = lx, pt[1]

                if py == ly and px == lx:
                    continue
                o.append(('L', px, py))
                lx, ly = px, py
        return o

    def pathBounds(self, points):
        t, r, b, l = (None,)*4
        for pt in self._canonPath(points):
            if pt == 'Z':
                pass
            elif t is None:
                r, t, l, b = pt[1:] + pt[1:]
            else:
                x, y = pt[1:]
                t, b = min(t, y), max(b, y)
                l, r = min(l, x), max(r, x)
        if t is None:
            return None
        return t, r, b, l

class SVG(_ContextBase):
    def __init__(self):
        super(SVG, self).__init__()
        self.__elts = []
        self.__defs = []
        self.__bounds = (0, 0, 0, 0)
        self._offset = (0, 0)
        self._save.append('_offset')
        self.__clipid = 0
        self.__enter__()

    def __bound(self, x, y):
        l, r, t, b = self.__bounds
        x += self._offset[0]; y += self._offset[1]
        self.__bounds = (min(x, l), max(x, r), min(y, t), max(y, b))

    def __fsAttrs(self, fill=None, stroke=None, stroke_width=None):
        ats = ''
        if fill is None:
            ats += ' fill="none"'
        else:
            ats += ' fill="%s"' % self.__rgb2css(fill)
            if len(fill) == 4:
                ats += ' fill-opacity="%g"' % fill[3]
        if stroke is not None:
            ats += ' stroke="%s"' % self.__rgb2css(stroke)
            if len(stroke) == 4:
                ats += ' stroke-opacity="%g"' % stroke[3]
        if stroke_width is not None:
            ats += ' stroke-width="%s"' % stroke_width
        return ats

    def __rgb2css(self, rgb):
        r, g, b = rgb[:3]
        return '#%02x%02x%02x' % (int(r * 255), int(g * 255), int(b * 255))

    def translate(self, x, y):
        self.__elts.append('<g transform="translate(%g,%g)">' % (x, y))
        self._offset = (self._offset[0] + x, self._offset[1] + y)
        self._unwind.append(lambda: self.__elts.append('</g>'))

    def rect(self, x, y, w, h, **kw):
        e = '<rect x="%g" y="%g" width="%g" height="%g"%s />' % \
            (x, y, w, h, self.__fsAttrs(**kw))
        self.__elts.append(e)
        self.__bound(x, y)
        self.__bound(x+w, y+h)

    def circle(self, x, y, r, **kw):
        e = '<circle cx="%g" cy="%g" r="%g"%s />' % \
            (x, y, r, self.__fsAttrs(**kw))
        self.__elts.append(e)
        self.__bound(x + r, y)
        self.__bound(x - r, y)
        self.__bound(x, y + r)
        self.__bound(x, y - r)

    def __mkD(self, points):
        d = []
        lx, ly = 0, 0
        for op in self._canonPath(points):
            if op == 'Z':
                d.append('Z')
            else:
                px, py = op[1], op[2]
                if op[0] == 'L' and px == lx:
                    d.append('V%g' % py)
                elif op[0] == 'L' and py == ly:
                    d.append('H%g' % px)
                else:
                    d.append('%s%g %g' % op)
                lx, ly = px, py
                self.__bound(px, py)
        return ' '.join(d)

    def path(self, points, **kw):
        e = '<path d="%s"%s />' % (self.__mkD(points), self.__fsAttrs(**kw))
        self.__elts.append(e)

    def clip(self, points):
        cid = 'clip%d' % self.__clipid
        self.__clipid += 1
        self.__defs.extend(['<clipPath id="%s">' % cid,
                            '  <path d="%s" />' % self.__mkD(points),
                            '</clipPath>'])
        self.__elts.append('<g clip-path="url(#%s)">' % cid)
        self._unwind.append(lambda: self.__elts.append('</g>'))

    def text(self, text, x, y, align, rotate=0, **kw):
        # Unfortunately, the various baseline adjustment properties
        # are not well supported, so we fake it by manually adjusting
        # the position relative to the line-height/font-size.
        # baseline = {'t': 'text-before-edge', 'c': 'central',
        #             'b': 'text-after-edge'}[align[0]]
        text_anchor = {'l': 'start', 'm': 'middle', 'r': 'end'}[align[1]]
        e = escape(text)
        extra = ''
        if align[0] == 't':
            extra += ' dy="%gpt"' % (self.font_size * .66)
        elif align[0] == 'c':
            extra += ' dy="%gpt"' % (self.font_size * .33)
        elif align[0] == 'b':
            pass
        else:
            raise ValueError('Unknown alignment %r' % align)
        if rotate:
            extra += ' transform="rotate(%g %g,%g)"' % (-rotate, x, y)
        kw.setdefault('fill', (0,0,0))
        e = '<text x="%g" y="%g" text-anchor="%s" font-size="%gpt"%s%s>%s</text>' % \
            (x, y, text_anchor, self.font_size, extra, self.__fsAttrs(**kw), e)
        self.__elts.append(e)

        # Guess bounds (more foolishness)
        w = 1.25 * (len(text) * self.font_size * 0.66)
        h = 1.25 * self.font_size
        wadj = {'l': 0, 'm': -w/2, 'r': -w}[align[1]]
        hadj = {'b': 0, 'c': h/2, 't': h}[align[0]]
        if rotate == 90:
            self.__bound(x + hadj,     y + wadj)
            self.__bound(x + hadj - h, y + wadj - w)
        else:
            self.__bound(x + wadj,     y + hadj)
            self.__bound(x + wadj + w, y + hadj - h)

    def write_to(self, fp,
                 attrs={'font-family':
                        '"Helvetica Neue", Helvetica, Arial, sans-serif'}):
        """Write the SVG output to fp."""

        self.__exit__()
        extra = ' '.join('%s=%s' % (k, quoteattr(v)) for k,v in attrs.items())
        l, r, t, b = self.__bounds
        print >>fp, '<svg version="1.1" width="%dpx" height="%dpx" viewBox="%g %g %g %g" %s>\n' % \
            (r - l, b - t, l, t, r - l, b - t, extra)
        if self.__defs:
            print >>fp, '<defs>'
            for elt in self.__defs:
                print >>fp, elt
            print >>fp, '</defs>'
        for elt in self.__elts:
            print >>fp, elt
        print >>fp, '</svg>'

class TikZ(_ContextBase):
    def __init__(self, x='%gin' % (1/90.0), y='%gin' % (1/90.0),
                 **attrs):
        """Create a new TikZ document.

        x and y specify the size of the x and y units.  Their default
        values match the physical size of SVG pixels.
        """
        super(TikZ, self).__init__()
        self.__gattrs = attrs.copy()
        self.__gattrs.update(x=str(x), y='-' + str(y))
        self.__o = []
        self.__enter__()

    def __mkColor(self, attr_name, spec):
        self.o(r'\definecolor{tmp%s}{rgb}{%g,%g,%g}' %
               ((attr_name,) + tuple(spec[:3])))
        attr = '%s=tmp%s' % (attr_name, attr_name)
        if len(spec) == 4:
            attr += ',%s opacity=%g' % (attr_name, spec[3])
        return attr

    def __fsOpts(self, fill=None, stroke=None, stroke_width=None):
        attrs = []
        if fill is not None:
            attrs.append(self.__mkColor('fill', fill))
        if stroke is not None:
            attrs.append(self.__mkColor('draw', stroke))
        if stroke_width is not None:
            attrs.append('line width=%s' % stroke_width)
        return ','.join(attrs)

    def o(self, code):
        self.__o.append(code)

    def translate(self, x, y):
        self.o(r'\begin{scope}[shift={(%g,%g)}]' % (x, y))
        self._unwind.append(lambda: self.o(r'\end{scope}'))

    def rect(self, x, y, w, h, **kw):
        self.o(r'\path[%s] (%g,%g) rectangle +(%g,%g);' %
               (self.__fsOpts(**kw), x, y, w, h))

    def circle(self, x, y, r, **kw):
        self.o(r'\path[%s] (%g,%g) circle (%g);' %
               (self.__fsOpts(**kw), x, y, r))

    def __mkPath(self, points):
        d = []
        for op in self._canonPath(points):
            if op == 'Z':
                d.append('-- cycle')
            else:
                if op[0] == 'L':
                    d.append('--')
                d.append('(%g,%g)' % op[1:])
        return ' '.join(d)

    def path(self, points, **kw):
        self.o(r'\path[%s] %s;' % (self.__fsOpts(**kw), self.__mkPath(points)))

    def clip(self, points):
        self.o(r'\begin{scope}')
        self.o(r'\clip %s;' % self.__mkPath(points))
        self._unwind.append(lambda: self.o(r'\end{scope}'))

    def text(self, text, x, y, align, rotate=0):
        attrs = [r'font=\fontsize{%g}{%g}\selectfont' %
                 (self.font_size, self.font_size*1.2)]
        if align != 'cm':
            attrs.append('inner sep=0')
            attrs.append('anchor=%s%s' %
                         ({'t': 'north', 'c': 'mid', 'b': 'south'}[align[0]],
                          {'l': ' west', 'm': '',    'r': ' east'}[align[1]]))
        if rotate:
            attrs.append('rotate=%g' % rotate)
        text = text.replace('%', '\\%')
        self.o(r'\path (%g,%g) node[%s] {%s};' % (x, y, ','.join(attrs), text))

    def write_to(self, fp):
        """Write the TikZ output to fp."""

        self.__exit__()
        print >>fp, r'\begin{tikzpicture}[%s]' % (
            ','.join('%s=%s' % kv for kv in self.__gattrs.items()))
        for line in self.__o:
            print >>fp, line
        print >>fp, r'\end{tikzpicture}'
