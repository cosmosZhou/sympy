from util import *
import axiom



@apply
def apply(self):
    exponent = set()
    base = []
    for arg in self.of(Mul, copy=True):
        b, e = arg.of(Pow)
        exponent.add(e)
        if len(exponent) > 1:
            return
        base.append(b)

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

