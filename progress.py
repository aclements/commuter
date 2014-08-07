import sys
import os
import threading

class ProgressReporter(object):
    def __init__(self, format_string, *args, **kwargs):
        self.__format_string, self.__args, self.__kwargs \
            = format_string, args, kwargs
        self.__dynamic = os.isatty(sys.stdout.fileno())
        self.__ended = False
        self.__last = None

        if self.__dynamic:
            self.__show()
            self.__bg_end = threading.Event()
            self.__bg_thread = threading.Thread(target=self.__bg)
            self.__bg_thread.daemon = True
            self.__bg_thread.start()

    def __del__(self):
        self.end()

    def end(self):
        if self.__ended:
            return
        self.__ended = True

        if self.__dynamic:
            self.__bg_end.set()
            self.__bg_thread.join()
        self.__show(final=True)

    def __show(self, final=False):
        assert final or self.__dynamic

        text = self.__format_string.format(*self.__args, **self.__kwargs)
        if text == self.__last:
            return
        self.__last = text

        buf = ""
        if self.__dynamic:
            buf += '\r'
            # Disable wrap
            buf += '\033[?7l'
        buf += text
        if self.__dynamic:
            # Re-enable wrap
            buf += '\033[?7h'
            # Clear to end of line
            buf += '\033[K'
            if final:
                buf += '\n'
            else:
                # Put cursor in wrap-around column.  If we print
                # anything more after this, it will immediately wrap
                # and print on the next line.  But we can still \r to
                # overwrite this line with another progress update.
                buf += '\033[999C '
        else:
            buf += '\n'
        sys.stdout.write(buf)
        sys.stdout.flush()

    def __bg(self):
        while not self.__bg_end.is_set():
            self.__bg_end.wait(0.5)
            self.__show()
