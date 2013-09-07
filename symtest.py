from simsym import *
from symtypes import *

def test():
    # Maps
    x = tmap(SInt, SBool).var("ib")
    x[1], x[2] = True, False
    assert x[1] == True
    assert x[2] == False

    # Maps of maps
    x = tmap(SInt, tmap(SInt, SBool)).var("iib")
    x[0][1], x[1][0] = True, False
    assert x[0][1] == True
    assert x[1][0] == False

    # Structs
    x = tstruct(a=SInt, b=SBool, c=SInt, d=SInt).var("s1")
    x.a, x.b, x.c = 1, True, x.d
    assert x.a == 1
    assert x.b == True
    assert x.c == x.d

    # Constant maps
    x = tmap(SInt, SInt).constVal(42)
    x[0] = 24
    assert x[0] == 24
    assert x[1] == 42

    # Nested constant maps
    t1 = tmap(SInt, SInt)
    x = tmap(SInt, t1).constVal(t1.constVal(42))
    assert x[0][0] == 42

    # Constant structs
    x = tstruct(a=SInt, b=SBool).var("s2", a=42)
    assert x.a == 42

    # Maps of constant structs
    t1 = tstruct(a=SInt, b=SBool)
    x = tmap(SInt, t1).constVal(t1.var("s3", a=42))
    assert x[0].a == 42
    assert x[0].b == x[1].b

    # Structs of constant maps
    t1 = tmap(SInt, SInt)
    x = tstruct(a=t1).var(a=t1.constVal(42))
    assert x.a[0] == 42

    # Assignment of structs in maps
    t1 = tstruct(a=SInt, b=SBool)
    x = tmap(SInt, t1).var()
    x[0] = t1.var(a=42, b=True)
    assert x[0].a == 42
    assert x[0].b == True

    # Assignment of structs in maps with symbolic index
    i = SInt.var()
    x[i] = t1.var(a=43, b=False)
    assert x[i].a == 43
    assert x[i].b == False

    # Assignment of a whole struct
    t1 = tstruct(a=SInt, b=SBool)
    t2 = tstruct(sub=t1)
    x = t2.var()
    x.sub = t1.var(a=42, b=True)
    assert x.sub.a == 42
    assert x.sub.b == True

    # Sets
    t1 = tset(SInt)
    assert not t1.empty().contains(1)

    # Lists
    ilist = tlist(SInt)
    l1 = ilist.var(_len = 0)
    l2 = ilist.var(_len = 0)
    l1.append(1)
    l2.append(1)
    assert l1[0] == l2[0]
    assert l1 == l2
    l2[0] = 2
    assert l1 != l2
    l2.append(1)
    assert l1 != l2
    l2.shift()
    assert l1 == l2

    # Dicts
    idict = tdict(SInt, SInt)
    d1 = idict.empty()
    d2 = idict.empty()
    assert d1 == d2
    d1[0] = 1
    assert d1 != d2
    d2[0] = 1
    assert d1 == d2
    d1[0] = 2
    assert d1 != d2
    del d1[0], d2[0]
    assert d1 == d2

list(symbolic_apply(test))
