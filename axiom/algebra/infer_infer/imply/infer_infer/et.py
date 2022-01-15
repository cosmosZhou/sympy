from util import *


@apply(given=None)
def apply(self):
    r, (p, q) = self.of(Infer[Infer])
    return Equivalent(self, Infer(r, Infer(p, q & r)))

@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, nonnegative=True)
    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Infer(Element(n, C), Infer(Element(n, A), Element(n, B))))

    Eq << Eq[-1].this.rhs.apply(algebra.infer.swap)

    Eq << Eq[-1].this.rhs.rhs.rhs.apply(sets.el.to.et.st.intersect)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.swap)


if __name__ == '__main__':
    run()
# created on 2019-10-09
