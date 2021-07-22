from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.swap.intlimit import limits_swap
    return Equal(self, limits_swap(Product, self))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)

    d = Symbol.d(integer=True)
    a = Symbol.a(integer=True)
    Eq << apply(Product[i:a + d:j + d, j:a:n](f[i] + g[i, j]))

    Eq << Eq[0].this.lhs.apply(algebra.product.bool)

    Eq << Eq[-1].this.lhs.expr.args[-1].arg.apply(sets.et.transform.i_lt_j.left_close)

    Eq << Eq[-1].this.rhs.apply(algebra.product.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.product.limits.swap)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Iverson_bracket
