from util import *


@apply
def apply(self):
    b, e = self.of(Pow)
    assert e % 2 == 0
    return Equal(self, (-b) ** e, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    n = Symbol(integer=True, even=True)
    Eq << apply((x - y) ** n)
    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.mul.neg)


if __name__ == '__main__':
    run()
# created on 2021-11-25
