from util import *


@apply(given=None)
def apply(self):
    r, (p, q) = self.of(Suffice[Suffice])
    return Equivalent(self, Suffice(r, Suffice(p, q & r)))

@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, nonnegative=True)
    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Suffice(Element(n, C), Suffice(Element(n, A), Element(n, B))))

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.swap)

    Eq << Eq[-1].this.rhs.rhs.rhs.apply(sets.el.to.et.st.intersect)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.swap)


if __name__ == '__main__':
    run()
