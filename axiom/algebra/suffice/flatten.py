from util import *


@apply(given=None)
def apply(self):
    A, (p, q) = self.of(Suffice[Basic, Suffice])
    return Equivalent(self, Suffice(A & p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Suffice(Element(x, A), Suffice(Element(y, B), Element(z, C))))

    Eq << Eq[-1].this.find(Suffice[~Suffice]).apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.to.ou)










if __name__ == '__main__':
    run()
