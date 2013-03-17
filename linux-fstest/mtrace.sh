#!/bin/sh

mkdir -p /tmp/nfs-export
./nfs-server.sh /tmp/nfs-export &
NFSPID="$!"
trap "kill $NFSPID" 0 1 2 3 14 15

/home/nickolai/proj/mtrace/x86_64-softmmu/qemu-system-x86_64 \
    -rtc clock=vm -mtrace-enable -mtrace-file mtrace.out \
    -hda ./fs.img \
    -smp 2 \
    -numa node -numa node \
    -kernel pk/arch/x86/boot/bzImage \
    -append "root=/dev/sda init=/init.sh console=ttyS0" \
    -m 256 \
    -serial mon:stdio \
    -nographic

# Unused for performance reasons:
#    -mtrace-calls \
#
