from util import *


@apply
def apply(equality, inequality):
    lhs, rhs = equality.of(Equal)
    x = inequality.of(Unequal[Probability, 0])

    _x, y = lhs.of(Probability).args

    if x != _x:
        _x, y = y, _x
    assert x == _x
    assert rhs == Probability(x) * Probability(y)

    return Equal(Probability(y, given=x), Probability(y))


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    given = Equal(Probability(x, y), Probability(x) * Probability(y))
    Eq << apply(given, Unequal(Probability(x), 0))

    Eq << Eq[-1].simplify()

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[1], y)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.collect(Probability(x))

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]

    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-15
