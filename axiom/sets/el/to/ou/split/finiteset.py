from util import *


@apply(given=None)
def apply(given):
    x, finiteset = given.of(Element)
    finiteset = finiteset.of(FiniteSet)

    return Equivalent(given, Or(*(Equal(x, e) for e in finiteset)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, {a, b}))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el.imply.ou.split.finiteset.two, simplify=False)

    Eq << Eq[-1].this.rhs.apply(sets.ou_eq.imply.el.finiteset)


if __name__ == '__main__':
    run()

# created on 2020-08-15
# updated on 2020-08-15
