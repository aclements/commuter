Commuter viewer
===============

This is a web-based interactive viewer for Commuter output files.

Use `mkdb` to convert an `mscan --check-testcases` output database
into the pre-processed format required by the viewer.

This is primarily a JavaScript library from which you can quickly
build a specialized interactive viewer.  A demo of its use can be
found in `demo.html` and `demo.js`.  The demo assumes databases are
present in `data/sv6.json` and `data/Linux.json`.  For example, to
generate the sv6 database from `mscan-sv6.out`, run the following in
the `viewer/` directory:

    mkdir -p data
    ./mkdb -o data --details mscan-sv6.out sv6

Chrome users: Chrome cannot run the demo directly from the file system
because it disallows XMLHttpRequest for local files.  You can serve
the local directory over HTTP using, for example:

    python -m SimpleHTTPServer [port]
