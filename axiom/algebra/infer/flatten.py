from util import *


@apply(given=None)
def apply(self, *, simplify=True):
    A, (p, q) = self.of(Infer[Basic, Infer])
    p &= A
    if simplify:
        p = p.simplify()
    return Equivalent(self, Infer(p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Infer(Element(x, A), Infer(Element(y, B), Element(z, C))))

    Eq << Eq[-1].this.find(Infer[~Infer]).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.to.ou)


if __name__ == '__main__':
    run()
# created on 2018-08-29
# updated on 2018-08-29
