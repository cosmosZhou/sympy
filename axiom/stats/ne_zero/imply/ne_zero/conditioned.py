from util import *


# given: Probability(x, y) != 0
# imply: Probability(x | y) != 0
@apply
def apply(given, wrt):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    probability = given.lhs
    p = probability.marginalize(wrt)

    return Unequal(Probability(p.arg | wrt), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0), y)

    Eq << stats.ne_zero.imply.et.apply(Eq[0])



    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << Eq[0].subs(Eq[-1])

    Eq << algebra.ne_zero.ne.imply.ne.scalar.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-10
