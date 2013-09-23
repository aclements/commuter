import simsym
import symtypes
import model

class Var(simsym.tstruct(val=simsym.SInt)):
    @model.methodwrap(val=simsym.SInt)
    def set(self, val):
        self.val = val

    @model.methodwrap()
    def get(self):
        return self.val

model_class = Var
