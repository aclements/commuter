import math
import collections

from context import SVG, TikZ

__all__ = "SVG TikZ test_bar test_blocks_horiz heat_map HeatMapObj".split()

def _frac2rgb(frac):
    """Convert frac to an RGB heat color (0 is red, 1 is green)."""
    def hsv2rgb(h, s, v):
        i = int(h * 6)
        f = h * 6 - i
        p = v * (1 - s);
        q = v * (1 - f * s)
        t = v * (1 - (1 - f) * s)
        i = i % 6
        if i == 0: return v, t, p
        if i == 1: return q, v, p
        if i == 2: return p, v, t
        if i == 3: return p, q, v
        if i == 4: return t, p, v
        if i == 5: return v, p, q
    full = (0.34065, 1, 0.91)
    none = (0, 0.8, 1)
    if frac == 1:
        return hsv2rgb(*full)
    return hsv2rgb(*_interN(none, full, frac / 2))

def _interN(a, b, v):
    def i1(idx):
        return a[idx] * (1 - v) + b[idx] * v
    return [a1 * (1 - v) + b1 * v for a1, b1 in zip(a, b)]

def _heat_fill(ctx, frac, points, cw, ch):
    """Fill region points with the color or pattern for frac.

    cw and ch must be the cell width and height; they will be used to
    scale the pattern for frac==1.
    """

    ctx.path(points, fill=_frac2rgb(frac))
    if frac < 1:
        return
    with ctx:
        ctx.clip(points)

        # Draw stripes
        t, r, b, l = ctx.pathBounds(points)
        delta, pad = max(r-l, b-t), cw
        color = _interN(_frac2rgb(1), (1,1,1), .3)
        # Sweep from left to right.  Compute base start X along t.
        bx = l - (b - t)
        # Adjust so bx-t+cw*N=0 so we pass through the origin.
        bx -= (bx - t) % cw
        while bx < r + cw:
            sx, sy, ex, ey = bx, t, bx + delta, t + delta
            if sx < l:
                # Trim start to follow left edge of bounding box
                sx, sy = l, sy + (l - sx)
            if ex > r:
                # Trim end to follow right edge of bounding box
                ex, ey = r, ey + (r - ex)
            if ey > b:
                # Trim end to follow bottom edge of bounding box
                ex, ey = ex + (b - ey), b
            ctx.path([('M', sx-pad, sy-pad), ('L', ex+pad, ey+pad)],
                     stroke=color, stroke_width=cw*math.sqrt(2)/4)
            bx += cw

def _shared_regions(testset):
    # Find failure regions
    regions = []
    for i, testcase in enumerate(testset):
        if testcase.shared:
            if regions and regions[-1][1] == i:
                regions[-1][1] = i+1
            else:
                regions.append([i, i+1])
    return regions, i + 1

def test_bar(ctx, testset, width, height):
    """Create a width x height bar showing test results.

    The bar is divided into vertical bands, with each showing the
    result of one test in testset.
    """

    regions, i = _shared_regions(testset)

    # Background
    ctx.rect(0, 0, width, height, fill=_frac2rgb(1))

    # Failures
    for (start, end) in regions:
        ctx.rect(width * start / float(i), 0,
                 width * (end-start) / float(i), height,
                 fill=_frac2rgb(0))

def test_blocks_horiz(ctx, testset, height, rows, col_width=None):
    """Create a horizontal block bar showing test results.

    The block bar is divided into rows blocks.  Test results are shown
    as colored blocks laid out from top to bottom, then left to right.
    Each block is height/rows by col_width pixels.  If col_width is
    omitted, it is set to the row width.
    """

    regions, i = _shared_regions(testset)
    ncols = (i + rows - 1) / rows
    last_col = i % rows
    mx, my = col_width, height / float(rows)
    if col_width is None:
        mx = my

    def region(start, end):
        last = end - 1
        sx, sy = divmod(start, rows)
        lx, ly = divmod(last, rows)
        if sx + 1 == sx and ly < sy:
            # Break in to two regions
            region(start, rows - sy)
            region(rows - sy, end)
            return
        # Generalized region.  Some of these points may turn out to be
        # the same.
        return [('M', mx * sx, my * sy),
                ('V', my * min(rows, sy + (end - start))), # Down
                ('H', mx * lx),                            # Right (bottom)
                ('V', my * (ly + 1)),                      # Up
                ('H', mx * (lx + 1)),                      # Right
                ('V', my * max(0, ly - (end - start))),    # Up
                ('H', mx * (sx + 1)),                      # Left (top)
                ('V', my * sy),                            # Down
                'Z']

    # Background
    ctx.path(region(0, i), fill=_frac2rgb(1))

    # Failures
    pts = []
    for (start, end) in regions:
        pts.extend(region(start, end))
    ctx.path(pts, fill=_frac2rgb(0))

def heat_map(ctx, table, cw, ch):
    """Create a heat map of table and return a HeatMapObj.

    cw and ch are with width and height of the cells.  The returned
    HeatMapObj lets the caller augment the heat map with labels.
    """

    # We go to great lengths here to render nicely in SVG/PDF engines
    # that approximate anti-aliasing using alpha blending (which seems
    # to be all of them except Acrobat).  If we simply render
    # rectangles with shared edges, the background color will bleed
    # through.  Hence, we need to overlap edges.  At the same time, if
    # two shapes overlap and share an edge, the bottom of the two
    # shapes will bleed through.  See
    # http://bugs.ghostscript.com/show_bug.cgi?id=689557 .  To fix
    # this, we bevel the edges of each cell, except where that bevel
    # would cover something already drawn.  Also, since the fills may
    # be complex, we trace the boundary of each region to minimize the
    # number of fill operations.

    filled = set()
    for y, row in enumerate(table.rows):
        for x, val in enumerate(row):
            if val is None or (x,y) in filled:
                continue

            # Treat (x,y) as the top-left coordinate on grid.
            # Trace clockwise around and bevel.
            edge, vert = [], collections.defaultdict(list)
            nx, ny = x, y

            # (dx, dy, checkdx, checkdy)
            dirs = [(+1, +0,  +0, -1), # Right
                    (+0, -1,  -1, -1), # Up
                    (-1, +0,  -1, +0), # Left
                    (+0, +1,  +0, +0)] # Down
            curdir = 1

            while (nx, ny) != (x, y) or len(edge) == 0:
                edge.append((nx, ny))
                for curdir in range(curdir - 1, curdir + 2):
                    dx, dy, checkdx, checkdy = dirs[curdir % 4]
                    check = (nx+checkdx, ny+checkdy)
                    if table.get(*check) != val:
                        if check not in filled and \
                           table.get(*check) is not None:
                            edge.append((nx + dx*0.5 + dy*0.5,
                                         ny + dy*0.5 - dx*0.5))

                        if dy > 0: vert[ny].append(nx)
                        nx += dx
                        ny += dy
                        if dy < 0: vert[ny].append(nx)
                        break
                else:
                    assert 0

            # Clean up degenerate convex bevels
            torm = []
            for i, (p1, p2, p3) in enumerate(zip(edge, edge[1:], edge[2:])):
                if p1 == p3:
                    torm.extend([i, i+1])
            for i in reversed(torm):
                del edge[i]

            # Add filled region to 'filled'
            this_filled = set()
            for fy, verts in vert.items():
                verts.sort()
                assert len(set(verts)) == len(verts)
                for left, right in zip(verts[::2], verts[1::2]):
                    for fx in range(left, right):
                        if table.get(fx, fy) == val:
                            this_filled.add((fx, fy))
            filled.update(this_filled)

            # Finally, trace the edge
            points = []
            for i, (ex, ey) in enumerate(edge):
                points.append(('M' if i == 0 else 'L', ex*cw, ey*ch))
            points.append('Z')

            _heat_fill(ctx, val, points, cw, ch)

    for i, row in enumerate(table.rows):
        if i % 4 == 0 and i != 0:
            ctx.path([('M', 0, i*ch), ('H', (len(table.rows) - i + 1)*cw)],
                      stroke=(1,1,1))
            ctx.path([('M', i*ch, 0), ('V', (len(table.rows) - i + 1)*ch)],
                      stroke=(1,1,1))

    width = max(pt[0]+1 for pt in filled) * cw
    height = max(pt[1]+1 for pt in filled) * ch
    return HeatMapObj(ctx, table, cw, ch, width, height)

class HeatMapObj(object):
    def __init__(self, ctx, table, cw, ch, w, h):
        self.__ctx, self.__table, self.__cw, self.__ch = ctx, table, cw, ch
        self.width, self.height = w, h

    def top_labels(self):
        for i, l in enumerate(self.__table.col_labels):
            self.__ctx.text(l, self.__cw * i + self.__ch * .5, -self.__ch * .25,
                            'cl', rotate=90)
        return self

    def left_labels(self):
        for i, l in enumerate(self.__table.row_labels):
            self.__ctx.text(l, -self.__cw * .25, self.__ch * i + self.__cw * .5,
                            'cr')
        return self

    def caption(self, caption):
        self.__ctx.text(caption, self.width / 2, self.height + self.__ch * 0.5,
                        'tm')
        return self

    def overlay(self, table):
        for y, row in enumerate(table.rows):
            for x, val in enumerate(row):
                if val is None:
                    continue
                self.__ctx.text(str(val), (x+0.5)*self.__cw, (y+0.5)*self.__ch,
                                'cm')
        return self

    def key(self, width, height, height100, segments=50, side='right'):
        ctx = self.__ctx
        height_rest = height - height100
        if side == 'right':
            lx, align = -(self.__cw * .25), 'cr'
        else:
            lx, align = width + (self.__cw * .25), 'cl'

        # Draw 100% box
        pts = [('M', 0, 0), ('H', width), ('V', height100), ('H', 0), 'Z']
        _heat_fill(ctx, 1, pts, self.__cw, self.__ch)
        ctx.path(pts, stroke=(0,0,0))

        # Draw gradient
        for segment in reversed(range(segments)):
            frac = segment / float(segments)
            top = height - ((segment + 1) / float(segments)) * height_rest
            ctx.rect(0, top, width, height - top, fill=_frac2rgb(frac))
        ctx.rect(0, height100, width, height - height100, stroke=(0,0,0))

        # Labels
        ctx.text('100%', lx, height100 * .5, align)
        ctx.text('0%', lx, height - height100 * .5, align)

