from util import *


@apply
def apply(self):
    (i, j), (j, S[0], i) = self.of(Product[Expr - Expr])

    return Equal(self, factorial(i))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Product[i:n](n - i))

    Eq << Eq[-1].this.rhs.apply(discrete.factorial.to.prod)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.subs.negate, i, n - i)


if __name__ == '__main__':
    run()
# created on 2022-01-15
