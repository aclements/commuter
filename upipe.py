import simsym
import symtypes
import model

SItembag = symtypes.tbag(simsym.SInt)

class UPipe(simsym.tstruct(elems=SItembag, nitem=simsym.SInt)):
    def _declare_assumptions(self, assume):
        super(UPipe, self)._declare_assumptions(assume)
        assume(self.nitem >= 0)

    @model.methodwrap(elem=simsym.SInt)
    def u_write(self, elem):
        self.elems.add(elem)
        self.nitem = self.nitem + 1

    @model.methodwrap()
    def u_read(self):
        if self.nitem == 0:
            return None
        else:
            e = self.elems.take()
            self.nitem = self.nitem - 1
            return e

model_class = UPipe
model_functions = [
    UPipe.u_write,
    UPipe.u_read,
]
