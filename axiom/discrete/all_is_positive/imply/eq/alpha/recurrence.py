from util import *
import axiom


@apply
def apply(given):
    xj, *limits = axiom.all_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 1
    x, _j = xj.of(Indexed)
    assert _j == j

    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


from axiom.discrete.imply.is_positive.alpha import alpha


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    Eq << apply(ForAll[i:1:n + 2](x[i] > 0))

    Eq << discrete.imply.suffice.alpha.recurrence.apply(alpha(x[:n + 2]))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

