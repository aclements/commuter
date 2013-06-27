import simsym
import model

class Counter(simsym.tstruct(counter=simsym.SInt)):
    __slots__ = ["counter"]

    @classmethod
    def _assumptions(cls, obj):
        return simsym.symand([super(Counter, cls)._assumptions(obj),
                              obj.counter >= 0])

    @model.methodwrap()
    def sys_inc(self):
        self.counter = self.counter + 1

    @model.methodwrap()
    def sys_dec(self):
        simsym.assume(self.counter > 0)
        self.counter = self.counter - 1

    @model.methodwrap()
    def sys_iszero(self):
        return self.counter == 0

model_class = Counter
model_functions = [
    Counter.sys_inc,
    Counter.sys_dec,
    Counter.sys_iszero,
]
