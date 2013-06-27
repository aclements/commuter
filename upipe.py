import simsym
import symtypes
import model

SItembag = symtypes.tbag(simsym.SInt)

class UPipe(simsym.tstruct(elems=SItembag, nitem=simsym.SInt)):
    @classmethod
    def _assumptions(cls, obj):
        return simsym.symand([super(UPipe, cls)._assumptions(obj),
                              obj.nitem >= 0])

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
