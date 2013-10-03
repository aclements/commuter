// XXX Show test code for test cases.

// XXX Clean up mixed 'self'/'xthis'

// Default order for calls
var CALL_SEQ = [
    'open', 'link', 'unlink', 'rename', 'stat',
    'fstat', 'lseek', 'close', 'pipe', 'read', 'write', 'pread', 'pwrite',
    'mmap', 'munmap', 'mprotect', 'memread', 'memwrite'];

//
// Reactive rendezvous
//

function Rendezvous(value) {
    this.value = value;
    this.reactives = [];
}

Rendezvous.prototype.get = function(refresh) {
    if (refresh._re_version === undefined)
        refresh._re_version = 0;
    this.reactives.push({version:refresh._re_version, refresh:refresh});
    return this.value;
};

Rendezvous.prototype.set = function(value) {
    if (value === this.value)
        return;
    this.value = value;
    var re = this.reactives;
    this.reactives = [];
    for (var i = 0; i < re.length; i++) {
        if (re[i].refresh._re_version === re[i].version) {
            ++re[i].refresh._re_version;
            re[i].refresh();
        }
    }
};

//
// Utilities
//

// Compare two calls
function compareCalls(call1, call2) {
    var i1 = CALL_SEQ.indexOf(call1), i2 = CALL_SEQ.indexOf(call2);
    if (i1 === -1) i1 = CALL_SEQ.length;
    if (i2 === -1) i2 = CALL_SEQ.length;
    if (i1 === i2)
        return call1 < call2 ? -1 : (call1 > call2 ? 1 : 0);
    return i1 - i2;
}

// Split callSeq into array of calls in canonical order
function splitCallSeq(callSeq) {
    var parts = callSeq.split('_');
    parts.sort(compareCalls);
    return parts;
}

// Compare two call sequences
function compareCallSeqs(cs1, cs2) {
    function convert(cs) {
        // Convert cs to a comparable string.  (This is slower than
        // comparing them directly, but imminently cache-able.)
        var r = compareCallSeqs.cache[cs];
        if (r === undefined) {
            var s = splitCallSeq(cs);
            r = '';
            for (var i = 0; i < s.length; i++) {
                var idx = CALL_SEQ.indexOf(s[i]);
                if (idx === -1)
                    r += s[i];
                else
                    r += '\x00' + String.fromCharCode(idx);
                r += '\x00';
            }
            compareCallSeqs.cache[cs] = r;
        }
        return r;
    }
    var s1 = convert(cs1), s2 = convert(cs2);
    return s1 < s2 ? -1 : (s1 > s2 ? 1 : 0);
}
compareCallSeqs.cache = {};

function fontSettings(elt) {
    elt = $(elt);
    return {font: elt.css('font'), fillStyle: elt.css('color'),
            apply: function(ctx) {
                ctx.font = this.font;
                ctx.fillStyle = this.fillStyle;
            }};
}

function setSelectionStyle(ctx, type) {
    ctx.lineWidth = 2;
    if (type === 'hover')
        ctx.strokeStyle = '#428bca';
    else
        ctx.strokeStyle = 'rgb(0,0,255)';
}

function bindSelectionEvents(canvas, coordToSel, selectionRv, hoverRv) {
    canvas = $(canvas);
    function setRv(rv, ev) {
        var offset = canvas.offset();
        var x = ev.pageX - offset.left, y = ev.pageY - offset.top;
        rv.set(coordToSel(x, y));
        return false;
    }
    canvas.click(setRv.bind(null, selectionRv));
    if (hoverRv) {
        canvas.mousemove(setRv.bind(null, hoverRv));
        canvas.mouseout(function() { hoverRv.set(null); });
    }
}

//
// Mscan database
//

function Database() {
    this.outputRv = new Rendezvous(Enumerable.empty());
    this.data = [];
    this.sources = [];
    this.loading = {};
    this.byid = {};
    this.templates = {};
    this.pending = [];
}

Database.prototype._load = function(uri, cb) {
    if (this.sources.indexOf(uri) != -1)
        return !this.loading[uri];

    this.sources.push(uri);
    this.loading[uri] = true;

    if (!this.loadDiv)
        this.loadDiv = $('<div>').addClass('viewer-loading').appendTo($('body'));
    var uriDiv = $('<div>').text('Loading ' + uri + '...').
        appendTo(this.loadDiv);

    var dbthis = this;
    $.getJSON(uri).
        always(function() {
            dbthis.loading[uri] = false;
            uriDiv.remove();
        }).
        done(function(json) {
            console.log('Loaded', uri);
            cb(json);
        }).
        fail(function(xhr, status, errorThrown) {
            // XXX More visible error?  Needs to be dismissable.
            console.log('Failed to load ' + uri + ': ' + status + ', ' +
                        errorThrown);
        });
    return false;
};

Database.prototype.loadMscan = function(uri) {
    var dbthis = this;
    return this._load(uri, function(json) {
        dbthis.pending.push({uri:uri, json:json});
        dbthis._processPending();
    });
};

Database.prototype._processPending = function() {
    var stillPending = [];
    for (var i = 0; i < this.pending.length; i++) {
        var p = this.pending[i];
        var testcases = this._tryDecompress(p.uri, p.json.testcases);
        if (testcases === null) {
            stillPending.push(p);
            continue;
        }
        testcases = this._expandStacks(testcases, p.json.stacks);
        testcases = this._addComputed(testcases);
        this._add(testcases);
    }
    this.pending = stillPending;
};

Database.prototype._add = function(recs) {
    // Full outer join recs with this.data on 'id'
    // XXX Always join in load order without overwrites
    for (var i = 0; i < recs.length; i++) {
        var rec = recs[i];
        var pre = this.byid[rec.id];
        if (pre === undefined) {
            this.data.push(rec);
            this.byid[rec.id] = rec;
        } else {
            $.extend(pre, rec);
        }
    }

    // Sort data
    function cmp(a, b) {
        return a < b ? -1 : (a > b ? 1 : 0);
    }
    this.data.sort(function(a, b) {
        return compareCallSeqs(a.calls, b.calls) || cmp(a.pathid, b.pathid) ||
            cmp(a.testno, b.testno) || cmp(a.runid, b.runid);
    });

    this.outputRv.set(Enumerable.from(this.data));
};

// Decompress json, which was loaded from uri.
//
// Returns null if this had to start an asynchronous template load.
Database.prototype._tryDecompress = function(uri, json) {
    if ('!template' in json) {
        // Template compression
        var tpath = uri.substring(0, uri.lastIndexOf('/')+1) + json['!template'];
        var template = this.templates[tpath];
        if (template === undefined) {
            // Load template and try again
            var dbthis = this;
            this._load(tpath, function(tjson) {
                dbthis.templates[tpath] = tjson;
                dbthis._processPending();
            });
            return null;
        }

        // Expand template
        template = this._tryDecompress(tpath, template);
        if (template === null)
            return null;
        var data = this._tryDecompress(uri, json['!data']);
        var out = [];
        for (var i = 0; i < template.length; i++)
            out.push($.extend({}, template[i], data[i]));
        return out;
    } else if ('!fields' in json) {
        // Table compression
        var fields = json['!fields'];
        var data = json['!data'];
        var out = [], prev = {}, weight = [];
        for (var i = 0; i < data.length; i++) {
            if (typeof data[i] === 'number') {
                // Run of data[i] copies of prev
                for (var j = 0; j < data[i]; j++)
                    out.push($.extend({}, prev));
                continue;
            }

            var deltamask = data[i][0];

            // Get or compute weight of deltamask
            var dw = weight[deltamask];
            if (dw === undefined) {
                dw = 0;
                for (var j = 0; j < fields.length; j++)
                    if (deltamask & (1 << j))
                        ++dw;
                weight[deltamask] = dw;
            }

            // Get initial object
            var obj = data[i][dw + 1] || {};

            // Fill fields
            var deltapos = 1;
            for (var j = 0; j < fields.length; j++) {
                if (deltamask & (1 << j))
                    obj[fields[j]] = data[i][deltapos++];
                else
                    obj[fields[j]] = prev[fields[j]];
            }

            out.push(obj);
            prev = obj;
        }
        return out;
    } else {
        return json;
    }
};

// Reverse deduplication of stacks in testcases
Database.prototype._expandStacks = function(testcases, stacks) {
    if (stacks === undefined)
        return testcases;
    var stackkeys = ['stack', 'stack1', 'stack2'];
    for (var tci = 0; tci < testcases.length; tci++) {
        var testcase = testcases[tci];
        for (var si = 0; si < testcase.shared.length; si++) {
            for (var ki = 0; ki < stackkeys.length; ki++) {
                var k = stackkeys[ki];
                var shared = testcase.shared[si];
                if (shared[k] === undefined)
                    continue;
                shared[k] = stacks[shared[k]];
            }
        }
    }
    return testcases;
}

// Add computed fields to testcases
Database.prototype._addComputed = function(testcases) {
    for (var i = 0; i < testcases.length; i++) {
        var testcase = testcases[i];
        testcase.path = testcase.calls + '_' + testcase.pathid;
        testcase.test = testcase.path + '_' + testcase.testno;
        testcase.id = testcase.test + '_' + testcase.runid;
        if (testcase.nshared !== undefined) {
            testcase.shared = new Array(testcase.nshared);
            delete testcase.nshared;
        }
    }
    return testcases;
}

//
// Query canvas
//

function QueryCanvas(parent, inputRv) {
    this.inputRv = this.curRv = inputRv;
    this.curSelRv = null;
    this.container = $('<div>').appendTo(parent);
}

QueryCanvas.prototype._add = function(op) {
    if (this.inputRv !== this.curRv)
        this._arrow();
    this.container.append(op.elt.addClass('viewer-operator'));
    this.curRv = op.outputRv;
    // Reset selection if parent selection changes
    if (this.curSelRv && op.resetSelection) {
        var parentSelRv = this.curSelRv;
        function monitorSelection() {
            parentSelRv.get(monitorSelection);
            op.resetSelection();
        }
        monitorSelection();
    }
    if (op.selectionRv)
        this.curSelRv = op.selectionRv;
    return this;
};

QueryCanvas.prototype._arrow = function() {
    this.container.
        append($('<div>').addClass('viewer-arrow'));
};

QueryCanvas.prototype.heatmap = function(pred, facets) {
    return this._add(new Heatmap(this.curRv, pred, facets, this.container));
};

QueryCanvas.prototype.heatbar = function(pred) {
    return this._add(new Heatbar(this.curRv, pred, this.container));
};

QueryCanvas.prototype.table = function(detailFn) {
    return this._add(new Table(this.curRv, detailFn));
};

//
// Heatmap
//

function Heatmap(inputRv, pred, facets, container) {
    this.inputRv = inputRv;
    this.pred = pred;
    this.facets = facets || function () { return ''; };
    this.fontSettings = fontSettings(container);

    this.elt = $('<div>').css({textAlign: 'center'});
    this.outputRv = new Rendezvous();
    this.selectionRv = new Rendezvous(null);
    this.hoverRv = new Rendezvous(null);
    this.elt.click(this.selectionRv.set.bind(this.selectionRv, null));
    this.refresh();
}

Heatmap.prototype.resetSelection = function() {
    this.selectionRv.set(null);
};

// Heatmap constants
Heatmap.CW = 16;
Heatmap.CH = 16;
Heatmap.PAD = Heatmap.CW / 2;

Heatmap.color = function(frac) {
    function hsv2css(h, s, v) {
        var i = Math.floor(h * 6);
        var f = h * 6 - i;
        var p = v * (1 - s);
        var q = v * (1 - f * s);
        var t = v * (1 - (1 - f) * s);
        switch (i % 6) {
        case 0: r = v, g = t, b = p; break;
        case 1: r = q, g = v, b = p; break;
        case 2: r = p, g = v, b = t; break;
        case 3: r = p, g = q, b = v; break;
        case 4: r = t, g = p, b = v; break;
        case 5: r = v, g = p, b = q; break;
        }
        return 'rgb(' + Math.floor(r * 255) + ',' + Math.floor(g * 255) + ',' +
            Math.floor(b * 255) + ')';
    }

    function inter(a, b, v) {
        return a * (1 - v) + b * v;
    }

    if (frac == 0)
        return hsv2css(0.34065, 1, 0.91);
    return hsv2css(inter(0.34065, 0,   0.5 + frac / 2),
                   inter(1,       0.8, 0.5 + frac / 2),
                   inter(0.91,    1,   0.5 + frac / 2));
};

Heatmap.prototype.refresh = function() {
    var hmthis = this;
    this.elt.empty();
    var input = this.inputRv.get(this.refresh.bind(this));

    // Get all calls, ordered by CALL_SEQ, then alphabetically.
    // XXX Maybe this shouldn't be symmetric.  For example, if my
    // input is for just one call set X_Y, then I shouldn't list both
    // X and Y on both the rows and columns.
    var calls = input.
        selectMany(function (testcase) { return testcase.calls.split('_'); }).
        distinct().
        orderBy(function (name) {
            var idx = CALL_SEQ.indexOf(name);
            if (idx >= 0)
                return '\x00' + String.fromCharCode(idx);
            return name;
        }).toArray();

    // Split input into facets
    var facets = 
        input.groupBy(this.facets, null, function (fLabel, testcases) {
            return {
                label: fLabel,
                // Split facet into cells
                cells: testcases.groupBy(
                    function (testcase) {  return testcase.calls; }, null,
                    function (tcCalls, testcases) {
                        // Compute cell location
                        var cellCalls = tcCalls.split('_');
                        var c1 = calls.indexOf(cellCalls[0]);
                        var c2 = calls.indexOf(cellCalls[1]);
                        if (c1 <= c2)
                            var x = calls.length - c2 - 1, y = c1;
                        else
                            var x = calls.length - c1 - 1, y = c2;

                        // Aggregate cell information
                        return testcases.aggregate(
                            {x:x, y:y, testcases:testcases,
                             total: 0, matched: 0},
                            function (sum, testcase) {
                                ++sum.total;
                                if (hmthis.pred(testcase))
                                    ++sum.matched;
                                return sum;
                            });
                    }).memoize()
            };
        }).memoize();

    // Create canvases, update selection, and do initial renders
    this._maxLabel = 0;
    facets.forEach(function (facet) {
        // Create canvas
        var div = $('<div>').css({display: 'inline-block'}).
            appendTo(hmthis.elt);
        var canvas = $('<canvas>').appendTo(div);

        // Activate canvas
        // XXX Support selecting a whole call, or a whole facet
        bindSelectionEvents(canvas, hmthis._coordToSel.bind(hmthis, facet),
                            hmthis.selectionRv, hmthis.hoverRv);

        // Label canvas
        var label = $('<div>').css({textAlign: 'center'}).text(facet.label).
            appendTo(div);

        // Keep selection across refreshes if possible
        if (hmthis.selectionRv.value &&
            hmthis.selectionRv.value.facet.label === facet.label)
            hmthis.selectionRv.value.facet = facet;

        // Set up facet object
        facet.calls = calls;
        facet.canvas = canvas[0];
        facet.labelDiv = label;
        hmthis._render(facet);
    });

    // Set up output
    this._setOutput(input);
};

Heatmap.prototype._coordToSel = function(facet, x, y) {
    var cx = Math.floor((x - facet.startX) / Heatmap.CW);
    var cy = Math.floor((y - facet.startY) / Heatmap.CH);
    if (cx < 0 || cy < 0 || cy > facet.calls.length - cx - 1)
        return null;
    return {facet:facet, x:cx, y:cy};
};

Heatmap.prototype._render = function(facet) {
    var CW = Heatmap.CW, CH = Heatmap.CH, PAD = Heatmap.PAD;
    var rerender = this._render.bind(this, facet);

    var calls = facet.calls;
    var ctx = facet.canvas.getContext('2d');
    var hover = this.hoverRv.get(rerender) || {};

    // Measure labels
    if (this._maxLabel === 0) {
        this.fontSettings.apply(ctx);
        for (var i = 0; i < calls.length; i++)
            this._maxLabel = Math.max(this._maxLabel,
                                      ctx.measureText(calls[i]).width);
    }
    var maxLabel = this._maxLabel;

    // Size (and clear) canvas
    var startX = maxLabel + PAD, startY = maxLabel + PAD;
    facet.startX = startX;
    facet.startY = startY;
    facet.canvas.width = startX + CW * calls.length + 5;
    facet.canvas.height = startY + CH * calls.length + 5;
    this.fontSettings.apply(ctx);

    // Tweak facet label layout
    facet.labelDiv.css({paddingLeft: startX, width: CW * calls.length});

    // Labels
    ctx.save();
    ctx.textBaseline = 'middle'
    ctx.save();
    ctx.rotate(-Math.PI / 2);
    for (var i = 0; i < calls.length; i++) {
        if (i === hover.x && hover.facet === facet)
            ctx.fillStyle = '#428bca';
        else
            ctx.fillStyle = this.fontSettings.fillStyle;
        ctx.fillText(calls[calls.length - i - 1],
                     -maxLabel, startX + i * CW + 0.5 * CW);
    }
    ctx.restore();
    ctx.textAlign = 'end';
    for (var i = 0; i < calls.length; i++) {
        if (i === hover.y && hover.facet === facet)
            ctx.fillStyle = '#428bca';
        else
            ctx.fillStyle = this.fontSettings.fillStyle;
        ctx.fillText(calls[i], startX - PAD, startY + i * CH + 0.5 * CH);
    }
    ctx.restore();

    // Draw cells
    ctx.save();
    ctx.translate(startX, startY);

    // Gray "unknown" background
    ctx.save();
    ctx.beginPath();
    ctx.moveTo(0, 0);
    for (var i = 0; i < calls.length; i++) {
        ctx.lineTo(CW * (calls.length - i), i * CH);
        ctx.lineTo(CW * (calls.length - i), (i + 1) * CH);
    }
    ctx.lineTo(0, calls.length * CH);
    ctx.fillStyle = "#ccc";
    ctx.shadowOffsetX = ctx.shadowOffsetY = 3;
    ctx.shadowBlur = 4;
    ctx.shadowColor = 'rgba(128,128,128,0.5)';
    ctx.fill();
    ctx.restore();

    // Known cells
    var clabels = [];
    facet.cells.forEach(function (cell) {
        ctx.fillStyle = Heatmap.color(cell.matched / cell.total);
        ctx.fillRect(cell.x * CW, cell.y * CH, CW, CH);
        if (cell.matched > 0)
            clabels.push({x:cell.x, y:cell.y,
                          label:cell.matched.toString()});
    });

    // Hover
    if (hover.facet === facet) {
        ctx.save();
        setSelectionStyle(ctx, 'hover');
        ctx.strokeRect(hover.x * CW, hover.y * CH, CW, CH);
        ctx.restore();
    }

    // Selection
    var sel = this.selectionRv.get(rerender) || {};
    if (sel.facet === facet) {
        ctx.save();
        setSelectionStyle(ctx);
        ctx.strokeRect(sel.x * CW, sel.y * CH, CW, CH);
        ctx.restore();
    }

    // Cell labels
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.font = (Heatmap.CH * 0.5) + 'px sans-serif';
    ctx.fillStyle = this.fontSettings.fillStyle;
    for (var i = 0; i < clabels.length; i++) {
        var cl = clabels[i];
        ctx.fillText(cl.label, (cl.x + 0.5) * CW, (cl.y + 0.5) * CH);
    }

    ctx.restore();
};

Heatmap.prototype._setOutput = function(input) {
    // Refresh output based on selection
    var sel = this.selectionRv.get(this._setOutput.bind(this, input)) || {};

    if (!sel.facet) {
        // Select everything by default
        this.outputRv.set(input);
        return;
    }
    this.outputRv.set(sel.facet.cells.selectMany(function(cell) {
        if (cell.x === sel.x && cell.y === sel.y)
            return cell.testcases;
        return [];
    }));
};

//
// Heat bar
//

function Heatbar(inputRv, pred, container) {
    this.inputRv = inputRv;
    this.pred = pred;
    this.fontSettings = fontSettings(container);

    this.elt = $('<div>').addClass('viewer-heatbar');
    this.llabel = $('<span>').appendTo(this.elt);
    this.canvas = $('<canvas>').appendTo(this.elt)[0];
    this.rlabel = $('<span>').appendTo(this.elt);
    this.blabel = $('<div>').appendTo(this.elt);
    this.selectionRv = new Rendezvous(null);
    this.hoverRv = new Rendezvous(null);
    bindSelectionEvents(this.canvas, this._coordToSel.bind(this),
                        this.selectionRv, this.hoverRv);
    this.elt.click(this.selectionRv.set.bind(this.selectionRv, null));
    this.outputRv = new Rendezvous();
    this.refresh();
}

Heatbar.prototype.resetSelection = function() {
    this.selectionRv.set(null);
};

Heatbar.prototype.refresh = function() {
    var self = this;
    var input = this.inputRv.get(this.refresh.bind(this));

    // Get statistics
    var stats = input.aggregate({total: 0, matched: 0},
                                function (sum, rec) {
                                    ++sum.total;
                                    if (self.pred(rec))
                                        ++sum.matched;
                                    return sum;
                                });
    this.stats = stats;

    // Set labels
    this.llabel.text(stats.total - stats.matched);
    this.rlabel.text(stats.matched);
    if (this.pred.predLabels) {
        this.llabel.text(this.llabel.text() + ' ' + this.pred.predLabels[0]);
        this.rlabel.text(this.rlabel.text() + ' ' + this.pred.predLabels[1]);
    }
    this.blabel.text(stats.total + ' total');

    // Size canvas
    var R = 10, MAX_W = 384, H = 25;
    var width = MAX_W * (1 - (R / (stats.total + R)));
    var factor = stats.total === 0 ? 0 : (width / stats.total);
    this.canvas.width = width + 2;
    this.canvas.height = H + 2;
    this.mid = 1 + (stats.total - stats.matched) * factor;

    this._render();

    this._setOutput(input);
};

Heatbar.prototype._coordToSel = function(x, y) {
    return (x >= this.mid + 1);
};

Heatbar.prototype._setOutput = function(input) {
    var sel = this.selectionRv.get(this._setOutput.bind(this, input));
    if (sel === null)
        this.outputRv.set(input);
    else if (sel)
        this.outputRv.set(input.where(this.pred));
    else
        this.outputRv.set(input.where(
            function (rec) { return !this.pred(rec) }.bind(this)));
};

Heatbar.prototype._render = function() {
    var rerender = this._render.bind(this);
    var stats = this.stats;
    var width = this.canvas.width - 2, height = this.canvas.height - 2;
    var ctx = this.canvas.getContext('2d');
    ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
    ctx.save();
    ctx.translate(1, 1);

    // Regions
    var mid = this.mid;
    ctx.fillStyle = Heatmap.color(0);
    ctx.fillRect(0, 0, width, height);
    ctx.fillStyle = Heatmap.color(1);
    ctx.fillRect(mid, 0, width - mid, height);

    function strokeRegion(rgn) {
        if (rgn === false)
            ctx.strokeRect(0, 0, mid, height);
        else if (rgn === true)
            ctx.strokeRect(mid, 0, width - mid, height);
    }

    // Hover and selection
    ctx.save();
    setSelectionStyle(ctx, 'hover');
    strokeRegion(this.hoverRv.get(rerender));
    setSelectionStyle(ctx);
    strokeRegion(this.selectionRv.get(rerender));
    ctx.restore();

    // Percentage labels
    function pct(val, x) {
        val = Math.round(val * 100);
        if (val == 0)
            return;
        val += '%';
        var tw = ctx.measureText(val).width;
        if (x - tw / 2 <= 0) {
            ctx.textAlign = 'left';
            ctx.fillText(val, 0, height / 2);
        } else if (x + tw / 2 >= width - 1) {
            ctx.textAlign = 'right';
            ctx.fillText(val, width - 1, height / 2);
        } else {
            ctx.textAlign = 'center';
            ctx.fillText(val, x, height / 2);
        }
    }
    this.fontSettings.apply(ctx);
    ctx.textBaseline = 'middle';
    pct(1 - (stats.matched / stats.total), mid / 2);
    pct(stats.matched / stats.total, (width + mid) / 2);

    ctx.restore();
};

//
// Table UI
//

function Table(inputRv, detailFn) {
    this.inputRv = inputRv;
    this.detailFn = detailFn || function () {};

    this.elt = $('<div>').addClass('datatable-wrapper');
    this.table = $('<table>').addClass('datatable').appendTo(this.elt);
    this.outputRv = new Rendezvous();
    this.limit = new Rendezvous(10);
    this.refresh();
}

Table.prototype.resetSelection = function() {
    this.limit.set(10);
};

Table.INCREMENT = 100;
Table.COL_ORDER = ['calls', 'path', 'test', 'id', 'shared'];
Table.HIDE = ['runid', 'pathid', 'testno'];
Table.FORMATTERS = {
    shared: function(val) {
        if (!$.isArray(val))
            return;
        if (val.length === 0)
            return $('<td>0 addrs</td>');
        return $('<td style="color:#c00">').text(val.length + ' addrs');
    },
    path: function(val) {
        var parts = val.split('_');
        var pathid = parts[parts.length - 1];
        return $('<td><span style="color:#888">...</span></td>').append(pathid);
    },
    test: function(val) {
        var parts = val.split('_');
        var testid = parts[parts.length - 1];
        return $('<td><span style="color:#888">...</span></td>').append(testid);
    },
    id: function(val) {
        var parts = val.split('_');
        var testid = parts[parts.length - 1];
        return $('<td><span style="color:#888">...</span></td>').append(testid);
    },
};
Table.NA = $('<td style="color:#ccc">NA</td>');
Table.fmtCell = function(row, colname) {
    var val = row[colname];
    var res = undefined;
    if (colname in Table.FORMATTERS) {
        try {
            res = Table.FORMATTERS[colname](val);
        } catch (e) {
            console.log('Formatter failed:', e);
        }
    }
    if (res === undefined) {
        if (val === undefined) {
            res = Table.NA.clone();
        } else if (typeof val === 'string') {
            res = $('<td>').text(val);
        } else {
            var text = JSON.stringify(val);
            if (text.length > 32)
                text = text.substring(0, 32) + '...';
            res = $('<td>').text(text);
        }
    }
    res.css({borderTop: '1px solid #ccc'});
    return res;
};

Table.prototype.refresh = function() {
    var input = this.inputRv.get(this.refresh.bind(this));
    this._render(input);
    this.outputRv.set(input);
};

Table.prototype._render = function(input) {
    var rerender = this._render.bind(this, input);
    var tthis = this;
    var table = this.table;
    var limit = this.limit.get(rerender);

    // Save expanded rows
    var expanded = {};
    $('tr', table).each(function () {
        var info = $(this).data('table-info');
        if (info && info.is(':visible'))
            expanded[$(this).data('table-rec').id] = true;
    });

    // Clear table
    table.empty();

    // Collect columns
    var cols = [], colSet = {};
    input.take(limit).forEach(function(rec) {
        // XXX Descend into object fields
        $.each(rec, function(colname) {
            if (Table.HIDE.indexOf(colname) === -1 && !colSet[colname]) {
                colSet[colname] = true;
                cols.push(colname);
            }
        });
    });

    // Sort columns
    cols.sort(function (a, b) {
        var ai = Table.COL_ORDER.indexOf(a), bi = Table.COL_ORDER.indexOf(b);
        if (ai === -1) ai = Table.COL_ORDER.length;
        if (bi === -1) bi = Table.COL_ORDER.length;
        if (ai === bi)
            return a === b ? 0 : (a < b ? -1 : 1);
        return ai - bi;
    });

    // Create table header
    var th = $('<tr>').appendTo($('<thead>').appendTo(table));
    $.each(cols, function () {
        th.append($('<th>').text(this).css({width: (100 / cols.length) + '%'}));
    });

    // Create table rows
    var prev = {};
    input.forEach(function(rec, index) {
        if (index == limit) {
            // Reached limit; add table expander
            table.append(
                $('<tr>').addClass('datatable-more').append(
                    $('<td>').attr({colspan: cols.length}).
                        text((input.count() - index) + ' more...')).
                    click(function() {
                        if (limit < Table.INCREMENT)
                            limit = 0;
                        limit += Table.INCREMENT;
                        tthis.limit.set(limit);
                    }));
            return false;
        }

        var tr = $('<tr>').addClass('datatable-row').appendTo(table);
        tr.data('table-rec', rec);

        // Create cells
        for (var i = 0; i < cols.length; i++) {
            var colname = cols[i];
            if (prev[colname] === rec[colname]) {
                tr.append($('<td>'));
            } else {
                prev = {};
                tr.append(Table.fmtCell(rec, colname));
            }
        }
        prev = rec;

        // Make row clickable
        tr.click(function() {
            if (!tr.data('table-info'))
                tthis._addDetail(tr, cols.length).hide();
            tr.data('table-info').slideToggle();
        });

        // Expand if previously expanded
        if (expanded[rec.id])
            tthis._addDetail(tr, cols.length);
    });
};

Table.prototype._addDetail = function(tr, ncols) {
    var ntr = $('<tr>').addClass('datatable-info'), div;
    ntr.append($('<td>').attr({colspan: ncols}).append(div = $('<div>')));
    tr.after(ntr).data('table-info', div);

    var rec = tr.data('table-rec');
    var detail = this.detailFn(rec);
    if (detail === undefined)
        detail = ($('<pre>').css({font: 'inherit', whiteSpace: 'pre-wrap'}).
                  text(JSON.stringify(rec, null, '  ')));
    div.append(detail);
    return div;
};

//
// Standard predicates
//

Predicate = {};

Predicate.conflicted = function(tc) {
    return tc.shared.length != 0;
};
Predicate.conflicted.predLabels = ['conflict-free', 'conflicted'];

//
// Setup
//

var database = new Database();

$(document).ready(function() {
    var qc = new QueryCanvas($('#container'), database.outputRv);
    qc.heatmap(Predicate.conflicted,
               function(tc) { return tc.runid; });
    qc.heatbar(Predicate.conflicted);
    qc.table(function(tc) {
        // Lazy load detail databases
        // XXX Load just the one this test case needs
        if (!database.loadMscan('data/sv6-details.json') ||
            !database.loadMscan('data/Linux-details.json'))
            return $('<span>').text('Loading details...');
    });

    database.loadMscan('data/sv6.json');
    database.loadMscan('data/Linux.json');
});
