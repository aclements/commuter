Commuter is an automated scalability testing tool that hunts down
unnecessary sharing in your code.  Unlike traditional scalability
testing, Commuter doesn't require handcrafted workloads or even
multicore hardware.  Starting with a high-level software interface
model written in Python -- not some esoteric specification language --
Commuter automatically generates thousands of test cases for your
interface and tests your implementation to root out the exact causes
and locations of unnecessary, scalability-limiting sharing.

Commuter is currently a research prototype.  It has been used to
successfully analyze an 18 call model of the POSIX file system and
virtual memory APIs and test the scalability of these calls in both
Linux and our research OS kernel, sv6.

Check out Commuter's [home page](http://pdos.csail.mit.edu/commuter/).

Quick start
-----------

To simplify getting up and running, Commuter includes a "setup" script
that can download and build all of Commuter's unusual dependencies
with default configurations, as well as both sv6 and Mtrace-enabled
Linux.  You can run `./setup all`, then jump straight to "Running the
POSIX model" below.  You can run `./setup` with different arguments to
install just some of the components.

Dependencies
------------

Commuter depends on several other software packages, which themselves
depend on other packages.  You can either use Commuter's setup script
to install these, or install them yourself.

* Z3 - Z3 is available from https://z3.codeplex.com/ .  As of this
  writing you'll need a nightly build, since Commuter depends on
  several bug fixes that are not in the stable 4.3.0 release.  You can
  download pre-built nightlies for various OSs from Z3's home page, or
  clone their unstable branch.

  You may either install Z3 system-wide, or set the environment
  variables `LD_LIBRARY_PATH` and `PYTHONPATH` to the local
  installation of Z3 before running Commuter.

  The results in the SOSP '13 paper were generated with Z3 commit
  `a60b53bfd` from the unstable branch, but it's likely that any
  nightly build will work.

* mtrace - Mtrace is our modified version of QEMU that Commuter uses
  to run tests and detect sharing in OS kernels.  Mtrace supports many
  other types of analyses, too, so it lives in a separate repository
  at

        git clone https://github.com/aclements/mtrace.git

  See mtrace's `README.md` for build instructions.

Operating systems
-----------------

Running an operating system in Commuter requires a small amount of
special support (specifically, hypercalls to mtrace).  Commuter has
been used with the following operating systems:

* Linux - The one and only.  Our mtrace-enabled version of Linux can
  be found at

        git clone https://github.com/aclements/linux-mtrace.git

  See the `README.md` in the mtrace repository for build instructions
  and more information on using mtrace with Linux.

* sv6 - The scalable POSIX-like operating system we built with the
  help of Commuter.  sv6 includes the RadixVM virtual memory system
  and the ScaleFS file system, published in EuroSys '13 and SOSP '13,
  respectively.  sv6 can be found at

        git clone https://github.com/aclements/sv6.git

Commuter components
-------------------

Commuter consists of several separate components designed to make it
easy to run (or re-run) just parts of the Commuter process.

* `spec.py` is the main entry point of Commuter, `spec.py` runs a
  model and its test generator and optionally produces commutativity
  conditions, test case code, and a machine-readable "model.out"
  summary of all explored paths and tests.  `spec.py` can also
  optionally analyze interface idempotence.

* `par-spec.py` is a parallel driver for `spec.py`.  Takes all the
  same arguments as `spec.py`.

* `split-testgen.py` splits test case code output into several files
  to enable parallel compilation.

* `par-mtrace.py` is a driver for running an OS kernel on the
  generated tests under mtrace to produce a memory access log.

* `par-mscan.py` is a driver for processing memory access logs to
  produce access conflict reports.

### Models

Commuter comes with several models.  The main POSIX file system and
virtual memory model is `models.fs`.  There are also several toy
models under `models/`.

Tools
-----

There are several tools for analyzing output files under `tools/`.

* `profile` generates statistics on a "model.out" file (and optionally
  its delta from another "model.out" file).

* `idem` slices and dices idempotence data in "model.out" files in
  various ways.

* `make-heatmaps` generates heat map figures from mscan output in
  either SVG or TikZ format.

### Viewer

There is a web-based interactive data visualizer in `viewer/`.  See
[its README](viewer/README.md).

Running the POSIX model
-----------------------

First,

1. Make sure mtrace is checked out in `../mtrace` and that you've
   compiled the mtrace version of QEMU as well as the tools in
   `../mtrace/mtrace-tools`.

2. Make sure sv6 is checked out in `../sv6`.  You *don't* need to
   compile it, since the below instructions compile it with special
   options.

3. Make sure linux-mtrace is checked out in `../linux-mtrace` and
   compiled.

Note that the we use an unconventional Linux setup.  To keep the
virtual machine minimal, we run it with no disk, completely from an
initramfs.  However, the initramfs does not contain a typical Linux
user-space; to keep the sv6 and Linux environments as similar as
possible, the initramfs contains the sv6 user-space, compiled for
Linux.  This is probably not the best setup in the long run, but it
was expedient.

### Generate test cases

    # Run model; go get lunch
    ./par-spec.py models.fs -t testgen.c -m model.out --max-tests-per-path 500
    # Split testgen.c for parallel build
    ./split-testgen.py -d ../sv6/libutil < testgen.c

Neither Linux nor sv6 support resting `reboot`, so if your goal is
only to examine cache line sharing, you can speed up `spec.py` by
passing `-f '!reboot'`.

Furthermore, sv6 does not have an on-disk file system, so `sync` and
`fsync` are no-ops in sv6.  To disable test generation for these as
well, pass `-f '!reboot,!sync,!fsync'` to `spec.py`.

### Check cache line sharing on sv6 (serial version)

    cd ../sv6
    make HW=mtrace RUN='fstest -t; halt' mtrace.out
    ../mtrace/mtrace-tools/mscan --check-testcases --kernel o.mtrace/kernel.elf > mscan-sv6.out

### Check cache line sharing on sv6 (parallel version)

    cd ../sv6
    ../commuter/par-mtrace.py -m xv6
    ../commuter/par-mscan.py --kernel o.mtrace/kernel.elf > mscan-sv6.out

### Check cache line sharing on Linux (serial version)

    cd ../sv6
    # Build the Linux initramfs for mtrace
    make HW=linuxmtrace
    # Run Linux kernel with tracing
    make HW=linuxmtrace KERN=../linux-mtrace/arch/x86_64/boot/bzImage RUN='fstest -t;halt' mtrace.out
    # Check sharing
    ../mtrace/mtrace-tools/mscan --kernel ../linux-mtrace/vmlinux --check-testcases > mscan-linux.out

### Check cache line sharing on Linux (parallel version)

    cd ../sv6
    make HW=linuxmtrace
    ../commuter/par-mtrace.py -m linux
    ../commuter/par-mscan.py --kernel ../linux-mtrace/vmlinux > mscan-linux.out

Now you can examine `mscan-sv6.out` or `mscan-linux.out` for
unnecessary sharing, or use the tools in `tools/` to generate
summaries, or fire up the [interactive viewer](viewer/README.md) in
`viewer/`.
