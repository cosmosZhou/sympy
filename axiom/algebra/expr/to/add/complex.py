from util import *


@apply
def apply(self):
    return Equal(self, Re(self) + Im(self) * S.ImaginaryUnit, evaluate=False)


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(z)

    return # the following will result recursive proving!
    Eq << algebra.expr.to.mul.expi.apply(z)


if __name__ == '__main__':
    run()
# created on 2018-03-11
