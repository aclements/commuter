import simsym
import model

class Counter(simsym.tstruct(counter=simsym.SInt)):
    def _declare_assumptions(self, assume):
        super(Counter, self)._declare_assumptions(assume)
        assume(self.counter >= 0)

    @model.methodwrap()
    def inc(self):
        self.counter = self.counter + 1

    @model.methodwrap()
    def dec(self):
        simsym.assume(self.counter > 0)
        self.counter = self.counter - 1

    @model.methodwrap()
    def iszero(self):
        return self.counter == 0

model_class = Counter
