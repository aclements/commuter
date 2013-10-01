// jQuery plugin to truncate blocks of text with ellipses and toggle
// them between collapsed and expanded state.
//
// jQuery Ellipsize is efficient, responds to window size changes,
// knows how to descend into nested tags, and uses visibility rather
// than text rewriting so ellipsized text does not shift around when
// toggled.
//
// The caller should put text to be truncated in a div with the
// desired max-height and overflow: hidden.
//
// The entry point of this plugin is
//   <jQuery collection>.ellipsize(action, [options])
//
// where action must be one of
//
// - apply: Ellipsize content of matched elements.
//
//   options.expand, if provided, must be a jQuery collection to
//   append after the visible region.  This defaults to
//   '<span>...</span>'.  This will be cloned and enclosed within a
//   div set to the span the space between the last visible word and
//   the right edge of the container, so it can include floats to
//   right-align elements.  When clicked, this will expand the
//   truncated region.
//
//   options.collapse, if provided, must be a jQuery collection to use
//   as the collapser for this region.  This defaults to
//   '<span>^</span>'.  It will be appended after the expanded region.
//
//   This has the side-effect of wrapping every word within the
//   matched elements in a span, including descending into
//   text-containing elements.
//
//   If the text contained in the region fits, this will neither
//   truncate it nor add the expander.
//
// - expand: Expand truncated regions.
//
//   This will delete the expander and append the collapser.  When
//   clicked, the collapser will collapse the region.
//
//   For regions that are not collapsed, this does nothing.
//
// - collapse: Collapse an expanded ellipsized region.
//
// - refresh: Refresh the truncation point and collapser placement for
//   the matched elements.
//
//   This is done automatically on window size changes, but if
//   something else causes a container to change size, call this to
//   manually refresh.
//
// Author: Austin Clements <aclements@csail.mit.edu>

(function ($) {
    // Do not descend into "metadata content" or "embedded content"
    var notext =
        ('base link meta noscript script style template title'
         + ' audio canvas embed iframe img math object svg video').split(/\s+/);

    // Wrap all text words under element 'parent' in spans.
    function spanify(parent) {
        $(parent).contents().each(function () {
            if (this.nodeType === 3) {
                var nnodes = [];

                var val = this.nodeValue;
                var wordRe = /[^-\u00ad\s]+[-\u00ad]?/g;
                var match, last;
                while ((match = wordRe.exec(val)) !== null) {
                    // Add preceding space
                    if (match.index > 0) {
                        nnodes.push(document.createTextNode(
                            val.substring(last, match.index)));
                    }
                    last = wordRe.lastIndex;

                    // Wrap word
                    var span = document.createElement('span');
                    span.setAttribute('class', 'ellipsize-part');
                    span.appendChild(document.createTextNode(match[0]));
                    nnodes.push(span);
                }
                if (last === undefined)
                    // No words.  Don't touch it.
                    return;
                // Final spaces
                nnodes.push(document.createTextNode(val.substring(last)));

                var parent = this.parentNode;
                for (var i = 0; i < nnodes.length; i++)
                    parent.insertBefore(nnodes[i], this);
                parent.removeChild(this);
            } else if (this.nodeType === 1) {
                // Element
                if (!(this.namespaceURI == '' ||
                      this.namespaceURI == 'http://www.w3.org/1999/xhtml'))
                    return;
                if (notext.indexOf(this.tagName) >= 0)
                    return;
                spanify(this);
            }
        });
    }

    // Find truncation point under element 'parent', modify span
    // visibility, insert expander.
    function collapse(parent) {
        var parent = $(parent);

        // Quick return if parent width and height have not changed
        var pwidth = parent.width(), pheight = parent.height();
        if (parent.data('ellipsize-width') == pwidth &&
            parent.data('ellipsize-height') == pheight)
            return;
        parent.data('ellipsize-width', pwidth);
        parent.data('ellipsize-height', pheight);

        unCollapse(parent);

        // Scan parts to find last that fits in parent
        var vlimit = parent.offset().top + parent.height();
        var parts = $('.ellipsize-part', parent);
        var lo = 0, hi = parts.length - 1;
        while (lo < hi) {
            var mid = Math.floor((lo + hi + 1) / 2);
            var q = $(parts[mid]);
            if (q.offset().top + q.height() < vlimit)
                lo = mid;
            else
                hi = mid - 1;
        }

        if (lo == parts.length - 1)
            // All visible
            return;

        // Compute horizontal clearance
        // XXX This underestimates the width for just about anything
        // interesting (floats, icon fonts).
        var ellipsis = parent.data('ellipsize-expand');
        var ewrapped = $('<span>').append(ellipsis.clone()).
            addClass('ellipsize-ellipsis');
        var clearance = ewrapped.appendTo(parent).width();
        ewrapped.remove();

        // Strip visible elements until there's enough clearance
        var right = parent.offset().left + parent.width();
        var left = 0;
        for (var hide = lo; hide > 0; hide--) {
            left = $(parts[hide]).offset().left;
            if (right - left >= clearance)
                break;
        }

        // Hide elements through first overflowed element.  We do this
        // via 'visibility' to prevent layout changes.
        for (var i = hide; i <= lo; i++) {
            $(parts[i]).css('visibility', 'hidden').addClass('ellipsize-hidden');
        }

        // Add ellipsis
        ewrapped.css({position: 'absolute', width: right - left,
                      cursor: 'pointer'}).
            insertBefore(parts[hide]);
        ewrapped.click(function() {
            parent.ellipsize('expand');
            return false;
        });
    }

    // Undo the effects of collapse(parent).
    function unCollapse(parent) {
        var parent = $(parent);

        // Reset visibility and remove old ellipsis
        $('.ellipsize-hidden', parent).css('visibility', '').
            removeClass('ellipsize-hidden');
        $('.ellipsize-ellipsis', parent).remove();

        // Clear width/height cache
        parent.data('ellipsize-width', '');
        parent.data('ellipsize-height', '');
    }

    var resizeInstalled = false;
    var defaultExpand = $('<span>...</span>');
    var defaultCollapse = $('<span>^</span>');

    $.fn.ellipsize = function(action, options) {
        options = options || {};

        if (action === 'apply') {
            this.addClass('ellipsize-container');
            this.data('ellipsize-expand', options.expand || defaultExpand);
            this.data('ellipsize-collapse', options.collapse || defaultCollapse);
            this.each(function() {
                // Enclose all words in spans
                spanify(this);
                // Record collapsed height
                $(this).data('ellipsize-max-height', this.style.maxHeight);
            });

            if (!resizeInstalled) {
                resizeInstalled = true;
                $(window).resize(function() {
                    $('.ellipsize-container').ellipsize('refresh');
                });
            }

            action = 'collapse';
        }

        if (action === 'expand') {
            unCollapse(this);
            // Clear max height
            this.css('max-height', 'none');
            // Add collapsers
            this.each(function () {
                var jthis = $(this);
                jthis.append(jthis.data('ellipsize-collapse').clone().
                             addClass('ellipsize-ellipsis').click(function () {
                                 jthis.ellipsize('collapse');
                                 return false;
                             }));
            });
            this.data('ellipsize-state', 'expanded');
        } else if (action === 'collapse') {
            this.each(function() {
                // Restore max height
                this.style.maxHeight = $(this).data('ellipsize-max-height');
                // Collapse
                collapse(this);
            });
            this.data('ellipsize-state', 'collapsed');
        } else if (action === 'refresh') {
            this.each(function() {
                if ($(this).data('ellipsize-state') === 'collapsed')
                    collapse(this);
            });
        } else {
            throw 'Unknown action: ' + action;
        }

        return this;
    };
}(jQuery));
