import simsym
import model

class Counter(model.Struct):
    __slots__ = ["counter"]

    def __init__(self):
        # XXX This name matters since it connects the initial counter
        # value of different Counter objects.  Will this scale to more
        # complex state?
        self.counter = simsym.SInt.var('Counter.v')
        simsym.assume(self.counter >= 0)

    def sys_inc(self, which):
        self.counter = self.counter + 1

    def sys_dec(self, which):
        simsym.assume(self.counter > 0)
        self.counter = self.counter - 1

    def sys_iszero(self, which):
        return self.counter == 0

model_class = Counter
model_functions = [
    Counter.sys_inc,
    Counter.sys_dec,
    Counter.sys_iszero,
]
