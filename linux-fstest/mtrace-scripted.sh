#!/bin/sh

mtracefile="$1"
diskfile="$2"
outfile="$3"
shift 3

/home/nickolai/proj/mtrace/x86_64-softmmu/qemu-system-x86_64 \
    -rtc clock=vm -mtrace-enable -mtrace-file "$mtracefile" \
    -mtrace-calls \
    -hda "$diskfile" \
    -smp 3 \
    -numa node -numa node \
    -kernel pk/arch/x86/boot/bzImage \
    -append "root=/dev/sda init=/init.sh console=ttyS0 $*" \
    -m 256 \
    -serial file:$outfile \
    -nographic

