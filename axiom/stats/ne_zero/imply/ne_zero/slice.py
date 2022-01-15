from util import *


@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    eq = given.lhs.arg
    x, _x = eq.args
    assert _x == pspace(x).symbol
    n = x.shape[0]
    t = Symbol(domain=Range(1, n))
    return Unequal(Probability(x[:t]), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    n = Symbol(domain=Range(2, oo))
    x = Symbol(real=True, shape=(n,), random=True)
    Eq << apply(Unequal(Probability(x), 0))

    t = Symbol(domain=Range(1, n))
    Eq << Eq[0].this.lhs.arg.apply(algebra.eq.imply.et.eq.block, t)

    Eq << stats.ne_zero.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-23
