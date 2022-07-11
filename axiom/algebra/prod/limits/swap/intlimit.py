from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.swap.intlimit import limits_swap
    return Equal(self, limits_swap(Product, self))


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Product[i:a + d:j + d, j:a:n](f[i] + g[i, j]))

    Eq << Eq[0].this.lhs.apply(algebra.prod.bool)

    Eq << Eq[-1].this.find(And).apply(sets.et_el.transform.i_lt_j.left_close)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.swap)

    


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Iverson_bracket
# created on 2020-03-08
# updated on 2022-01-28
