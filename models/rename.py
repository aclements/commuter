# The simplified rename model from the SOSP '13 paper

import simsym
import symtypes
import model
import errno

SymByte     = simsym.tuninterpreted('SymByte')
SymInode    = simsym.tstruct(data  = symtypes.tlist(SymByte),
                             nlink = simsym.SInt)
SymIMap     = simsym.tmap(simsym.SInt, SymInode)
SymFilename = simsym.tuninterpreted('Filename')
SymDir      = symtypes.tdict(SymFilename, simsym.SInt)

class Rename(simsym.tstruct(
        fname_to_inum=SymDir,
        inodes=SymIMap)):

    @model.methodwrap(src=SymFilename, dst=SymFilename)
    def rename(self, src, dst):
        if simsym.symnot(self.fname_to_inum.contains(src)):
            #return (-1, errno.ENOENT)
            return -1
        if src == dst:
            return 0
        if self.fname_to_inum.contains(dst):
            self.inodes[self.fname_to_inum[dst]].nlink -= 1
        self.fname_to_inum[dst] = self.fname_to_inum[src]
        del self.fname_to_inum[src]
        return 0

model_class = Rename
