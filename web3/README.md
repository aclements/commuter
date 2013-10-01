Building
--------

Run `make` and browse to dist/index.html.  `make` sets up hard-links
for most files, so they can be edited without having to run-run
`make`.

Installing Bootstrap 3.0.0
--------------------------

This is what I had to do to build and install Bootstrap under Debian
jessie.

Download https://github.com/twbs/bootstrap/archive/v3.0.0.zip and
unpack it.  Install Debian's nodejs and npm packages (I had to install
npm from unstable, but its dependencies came almost exclusively from
testing).  Create a wrapper script called "node" in your $PATH that
invokes /usr/bin/nodejs.  This is apparently the legacy name of the
nodejs binary and I found that a few packages still used it.  Install
grunt and Bootstrap dependencies.  I did this all locally, since I
didn't want npm mucking with my system:

  npm install grunt-cli
  npm install
  # Undeclared dependency from js-yaml?
  npm install esprima

Finally, build Bootstrap and copy its output

  node_modules/grunt-cli/bin/grunt dist
  cd ..
  mv bootstrap-3.0.0/dist/* .
