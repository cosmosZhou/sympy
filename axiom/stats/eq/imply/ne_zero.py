from util import *


@apply
def apply(given):
    (x, y), rhs = given.of(Equal[Conditioned])
    return Unequal(Probability(y), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, x))

    Eq << stats.eq.imply.eq.probability.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.lhs.apply(stats.probability.to.mul)

    Eq << algebra.eq.imply.ne_zero.domain_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-14
