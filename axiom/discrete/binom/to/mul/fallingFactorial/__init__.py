from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)

    return Equal(self, FallingFactorial(n, k) / Factorial(k))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n + 1))
    Eq << apply(binomial(n, k))

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.lhs.apply(discrete.binom.to.mul)

    #Eq << Eq[-1] * Factorial(k)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.prod)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.prod)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.lhs.args[0].apply(algebra.prod.limits.subs.negate, i, n - i)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(algebra.prod.limits.subs.negate, i, n - i)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.prod.limits.complement)


if __name__ == '__main__':
    run()

# created on 2020-02-28

from . import doit
