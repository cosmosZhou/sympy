from util import *


@apply
def apply(self):
    args = self.of(Mul)
    return Equal(self, Piecewise((self, And(*(Unequal(arg, 0) for arg in args))), (0, True)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x * y)

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(algebra.ne_zero.ne_zero.given.ne_zero)

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.ou_is_zero.given.mul_is_zero)


if __name__ == '__main__':
    run()
# created on 2018-01-30
# updated on 2018-01-30
