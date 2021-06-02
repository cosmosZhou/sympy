from util import *
import axiom


@apply
def apply(given):
    from axiom.discrete.K.to.add.definition import K
    xj, *limits = axiom.all_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 1
    x, _j = xj.of(Indexed)
    assert _j == j

    return Greater(K(x[:n]), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(ForAll[i:1:n](x[i] > 0))

    Eq << discrete.imply.suffice.is_positive.K.apply(x[:n])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

