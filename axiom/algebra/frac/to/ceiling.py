from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)

    return Equal(fraction, x + ceiling(-x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    Eq << apply(frac(x))

    Eq << Eq[-1].this.lhs.apply(algebra.frac.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.ceiling.to.add.frac)

    Eq << Eq[-1].this.find(FractionalPart).apply(algebra.frac.to.add)

if __name__ == '__main__':
    run()
# created on 2019-05-14
