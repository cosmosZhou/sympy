from util import *
import axiom



@apply
def apply(self):
    exponent = []
    base = set()
    for arg in self.of(Mul, copy=True):
        b, e = arg.of(Pow)
        base.add(b)
        if len(base) > 1:
            return
        exponent.append(e)

    base, *_ = base

    return Equal(self, base ** Add(*exponent), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    t = Symbol.t(real=True)
    Eq << apply(t ** x * t ** y)

    Eq << Eq[-1].this.rhs.apply(algebra.pow.to.mul.split.exponent)


if __name__ == '__main__':
    run()

