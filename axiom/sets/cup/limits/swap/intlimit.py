from util import *
import axiom

from axiom.algebra.sum.limits.swap.intlimit import limits_swap
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, limits_swap(self))


@prove
def prove(Eq):
    from axiom import sets
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    f = Symbol.f(shape=(oo,), etype=dtype.real)
    g = Symbol.g(shape=(oo, oo), etype=dtype.real)

    d = Symbol.d(integer=True)
    a = Symbol.a(integer=True)

    Eq << apply(Cup[i:a + d:j + d, j:a + 1:n](f[i] & g[i, j]))

    Eq << Eq[0].this.lhs.apply(sets.cup.piecewise)

    Eq << Eq[-1].this.lhs.function.args[0].cond.apply(sets.et.transform.i_lt_j)

    Eq << Eq[-1].this.rhs.apply(sets.cup.piecewise)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.swap)


if __name__ == '__main__':
    run()

