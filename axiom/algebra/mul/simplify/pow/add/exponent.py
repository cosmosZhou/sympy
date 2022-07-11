from util import *


@apply
def apply(self):
    from axiom.algebra.mul.to.pow.add.exponent import determine_args
    ret, others = determine_args(self.of(Mul))
    assert others

    return Equal(self, ret * Mul(*others), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, t, z = Symbol(real=True)
    Eq << apply(t ** x * t * z)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.pow.to.mul.split.exponent)
    


if __name__ == '__main__':
    run()
# created on 2022-07-07
