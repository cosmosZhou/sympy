from util import *


@apply
def apply(given, w):
    lhs, *limits = given.of(All[Equal[0]])
    factor = w[tuple(i for i, *_ in limits)]

    return Equal(Sum(lhs * factor, *limits), 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), complex=True)
    w = Symbol.w(complex=True, shape=(oo,))
    Eq << apply(All[i:n](Equal(f(i), 0)), w=w)

    Eq << Eq[0].this.function * w[i]

    Eq << algebra.all_is_zero.imply.sum_is_zero.apply(Eq[-1])

    


if __name__ == '__main__':
    run()