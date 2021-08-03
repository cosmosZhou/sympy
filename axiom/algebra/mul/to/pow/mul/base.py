from util import *


@apply
def apply(self):
    exponent = set()
    base = []
    unrealCount = 0
    for arg in self.of(Mul):
        b, e = arg.of(Pow)
        exponent.add(e)
        if len(exponent) > 1:
            return
        if not b.is_extended_real:
            unrealCount += 1
        base.append(b)
    assert unrealCount < 2
    exponent, *_ = exponent

    return Equal(self, Mul(*base) ** exponent, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    t = Symbol.t(integer=True)
    Eq << apply(x ** t * y ** t)

    Eq << Eq[-1].this.rhs.apply(algebra.pow.to.mul.split.base)


if __name__ == '__main__':
    run()

