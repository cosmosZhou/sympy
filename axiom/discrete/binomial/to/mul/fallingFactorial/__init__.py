from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)

    return Equal(self, FallingFactorial(n, k) / Factorial(k))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(domain=Range(0, n + 1))
    Eq << apply(binomial(n, k))

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.product)

    Eq << Eq[-1].this.lhs.apply(discrete.binomial.to.mul)
    Eq << Eq[-1] * Factorial(k)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.product)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.product)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.lhs.args[0].apply(algebra.product.limits.subs.negate, i, n - i)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(algebra.product.limits.subs.negate, i, n - i)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.product.limits.complement)


if __name__ == '__main__':
    run()

from . import doit