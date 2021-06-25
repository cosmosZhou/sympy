from util import *


@apply(given=None)
def apply(self):
    A, (p, q) = self.of(Suffice[Basic, Suffice])
    return Equivalent(self, Suffice(A & p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    C = Symbol.C(etype=dtype.real)
    Eq << apply(Suffice(Contains(x, A), Suffice(Contains(y, B), Contains(z, C))))

    Eq << Eq[-1].this.find(Suffice[~Suffice]).apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.to.ou)

    

    

    

    


if __name__ == '__main__':
    run()