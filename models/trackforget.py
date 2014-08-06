import simsym
import symtypes
import model

SEventList = symtypes.tlist(simsym.SInt)

class Tracker(simsym.tstruct(events=SEventList, forgot=simsym.SBool)):
    def _eq_internal(self, o):
        if type(self) != type(o):
            return NotImplemented
        return simsym.symand([self.forgot == o.forgot,
                              simsym.symor([self.forgot,
                                            self.events == o.events])])

    @model.methodwrap()
    def track(self):
        self.events.append(model.cur_thread())

    @model.methodwrap()
    def report(self):
        if self.forgot:
            return SEventList.var(_len = 0)
        return self.events

    @model.methodwrap()
    def forget(self):
        self.forgot = True

model_class = Tracker
