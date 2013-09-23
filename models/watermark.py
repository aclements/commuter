import simsym
import symtypes
import model

class Watermark(simsym.tstruct(val=simsym.SInt)):
    @model.methodwrap(val=simsym.SInt)
    def put(self, val):
        if val > self.val:
            self.val = val

    @model.methodwrap()
    def max(self):
        return self.val

model_class = Watermark
