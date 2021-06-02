from util import *
import axiom



@apply
def apply(self):
    negativeOne, flr = self.of(Mul, copy=True)
    assert negativeOne == -1
    x = flr.of(Ceiling)
    return Equal(self, floor(-x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    Eq << apply(-ceiling(x))

    Eq << Eq[0].this.rhs.apply(algebra.floor.to.mul.ceiling)


if __name__ == '__main__':
    run()
