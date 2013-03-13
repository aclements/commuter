#!/bin/bash
#
# To mount this NFS server from a qemu VM, run:
#
#    mount -t nfs -o nolock,vers=3,proto=tcp,mountport=21349,port=21349 10.0.2.2:/export/dir /mnt/x
#

if [ "x$1" = "x" ]; then
    echo "Usage: $0 directory"
    exit 1
fi

exec unfsd -u -t -p -n 21349 -m 21349 -s -l 127.0.0.1 -d -e <(echo "$1 127.0.0.1(rw,no_root_squash,insecure)")

