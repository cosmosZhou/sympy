from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Product)
    return Equal(self, Product[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    i = Symbol.i(integer=True)
    f = Function.f(real=True)
    Eq << apply(Product[i](f(i)))

    n = Symbol.n(integer=True, nonnegative=True)
    Eq << algebra.product.limits.negate.apply(Product[i:-n:n + 1](f(i)))

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.product)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.product)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()