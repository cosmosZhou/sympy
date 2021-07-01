from util import *


@apply(simplify=False)
def apply(self, simplify=True):
    from axiom.sets.contains.imply.ou.split.union import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A | B))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.et.split.union)

    


if __name__ == '__main__':
    run()

