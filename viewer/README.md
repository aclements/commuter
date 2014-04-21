Commuter viewer
===============

This is a web-based interactive viewer for Commuter output files.  You
can use the simple pre-built viewer in `index.html` or build a
specialized viewer using `viewer.js` and LINQ directly.

Before you can use the viewer, you must convert the output of `mscan
--check-testcases` to a pre-processed format using `mkdb`.  The demo
viewer expects these databases to be present in `data/sv6.json` and
`data/Linux.json`.  For example, to generate these from
`mscan-sv6.out` and `mscan-linux.out`, run the following in the
`viewer/` directory:

    mkdir -p data
    ./mkdb -o data mscan-sv6.out sv6
    ./mkdb -o data mscan-linux.out Linux

(It's okay if you only generate one of these; the viewer will show
whatever it can find.)

Then, fire up a local web server:

    python -m SimpleHTTPServer 8000

And point your web browser at http://localhost:8000 .
