from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_random
    assert rhs.is_random
    return Equal(Probability(lhs), Probability(rhs))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    p, q = Symbol(shape=(n,), integer=True, random=True)

    Eq << apply(Equal(p[i], q[i]))

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2020-12-13
