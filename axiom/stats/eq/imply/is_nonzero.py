from util import *


@apply
def apply(given):    
    (x, y), rhs = given.of(Equal[Conditioned])    
    return Unequal(Probability(y), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    Eq << apply(Equal(x | y, x))

    Eq << stats.eq.imply.eq.probability.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.lhs.apply(stats.probability.to.mul)

    Eq << algebra.eq_mul.imply.is_nonzero.apply(Eq[-1])


if __name__ == '__main__':
    run()