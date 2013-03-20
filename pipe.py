import simsym
import symtypes
import model

class Pipe(model.Struct):
    __slots__ = ['elems', 'nread']
    ListOfInt = symtypes.tlist(simsym.SInt)

    def __init__(self):
        self.elems = self.ListOfInt.any('Pipe.elems')
        self.nread = simsym.SInt.any('Pipe.nread')

        simsym.assume(self.nread >= 0)
        simsym.assume(self.nread <= self.elems.len())

    def write(self, which):
        elem = simsym.SInt.any('Pipe.write[%s].data' % which)
        self.elems.append(elem)

    def read(self, which):
        if self.elems.len() == self.nread:
            return None
        else:
            e = self.elems[self.nread]
            self.nread = self.nread + 1
            return e

