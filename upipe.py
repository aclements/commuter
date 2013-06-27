import simsym
import symtypes
import model

class UPipe(model.Struct):
    __slots__ = ['elems', 'nitem']
    SItembag = symtypes.tbag(simsym.SInt)

    def __init__(self):
        self.elems = self.SItembag.var('UPipe.items')
        self.nitem = simsym.SInt.var('UPipe.nitem')
        simsym.assume(self.nitem >= 0)

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
