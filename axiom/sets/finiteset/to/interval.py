from util import *


@apply
def apply(self):
    args = self.of(FiniteSet)
    size = len(args)
    m, *args = args

    for a in args:
        if a < m:
            m = a
    M = m + size - 1

    return Equal(self, Range(m, M + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol(integer=True)

    Eq << apply(FiniteSet(a, a + 1, a + 2, a + 3))

    Eq << Element(a, Eq[0].rhs, plausible=True)

    Eq << Element(a + 1, Eq[0].rhs, plausible=True)

    Eq << sets.el.el.imply.subset.finiteset.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Element(a + 2, Eq[0].rhs, plausible=True)

    Eq << sets.el.subset.imply.subset.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Element(a + 3, Eq[0].rhs, plausible=True)

    Eq.subset = sets.el.subset.imply.subset.apply(Eq[-1], Eq[-2], simplify=None)

    Eq.supset = Supset(*Eq.subset.args, plausible=True)

    Eq << sets.supset.given.all_el.apply(Eq.supset)

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit)

    Eq <<= Eq.supset & Eq.subset


if __name__ == '__main__':
    run()

# created on 2018-04-24
# updated on 2018-04-24
