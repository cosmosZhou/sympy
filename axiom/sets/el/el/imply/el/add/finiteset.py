from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    S0 = S0.of(FiniteSet)
    S1 = S1.of(FiniteSet)
    S = {a + b for a in S0 for b in S1}


    return Element(x0 + x1, S)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x0, x1, a, b, c, d, e = Symbol(integer=True)
    Eq << apply(Element(x0, {a, b, c}), Element(x1, {d, e}))

    Eq << sets.el.imply.ou.split.finiteset.apply(Eq[0])

    Eq << sets.el.imply.ou.split.finiteset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.args[1].apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.find(And).apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.args[2].apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.args[3].apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.find(And).apply(algebra.et.imply.ou, simplify=None)

    Eq << Eq[-1].this.args[4].apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.args[5].apply(algebra.eq.eq.imply.eq.add)

    Eq << sets.el.given.ou.split.finiteset.apply(Eq[2])


if __name__ == '__main__':
    run()