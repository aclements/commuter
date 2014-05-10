def sort_calls(calls):
    """Sort a set of function names into a pleasing order.

    This sorts non-POSIX names alphabetically, followed by POSIX names
    grouped and ordered in a reasonable way.
    """

    posix_calls = [
        # Things that deal with names
        'open', 'link', 'unlink', 'rename', 'stat',
        # Things that deal with FDs
        'fstat', 'lseek', 'close', 'pipe', 'read', 'write', 'pread', 'pwrite',
        # VM
        'mmap', 'munmap', 'mprotect', 'memread', 'memwrite']
    return sorted(calls, key=lambda c: (
        c in posix_calls, posix_calls.index(c) if c in posix_calls else c))
