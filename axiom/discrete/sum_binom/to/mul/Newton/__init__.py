from util import *


@apply
def apply(self):
    ((n, k), S[k], (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Symbol * Pow])
    assert a == 0 or a == 1
    return Equal(self, n * (x + 1) ** (n - 1) * x)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k))

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.binom)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)





if __name__ == '__main__':
    run()
# created on 2021-11-25
from . import deux
from . import trois
from . import quatre
