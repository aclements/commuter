Commuter viewer
===============

This is a web-based interactive viewer for Commuter output files.  You
can use the simple pre-built viewer or build a specialized viewer
using `viewer.js` and LINQ directly.


Usage
=====

From the `viewer/` directory, run

    ./view <paths to mscan databases>

This will load in the specified mscan databases, start an HTTP server
on a random port, and point your default browser at it.  See `./view
--help` for additional options.


Building a custom/static viewer
===============================

`view` is a convenient wrapper, but the viewer can run from any
regular, static web server.  To build a custom viewer, first convert
the output of `mscan --check-testcases` to a pre-processed format
using `mkdb`.  The demo viewer in `index.js` expects these databases
to be present in `data/sv6.json` and `data/Linux.json`.  For example,
to generate these from `mscan-sv6.out` and `mscan-linux.out`, run the
following in the `viewer/` directory:

    mkdir -p data
    ./mkdb -o data mscan-sv6.out sv6
    ./mkdb -o data mscan-linux.out Linux

(It's okay if you only generate one of these; the viewer will show
whatever it can find.)

Then, fire up a local web server in the `viewer/` directory:

    python -m SimpleHTTPServer 8000

And point your web browser at http://localhost:8000 .
