from util import *

import axiom


@apply
def apply(self):
    x = self.of(Softmax)
    return Equal(self, exp(x) / ReducedSum(exp(x)))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)

    Eq << apply(softmax(x))

    y = Symbol.y(softmax(x))

    i = Symbol.i(integer=True)

    Eq << y[i].this.definition

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()
