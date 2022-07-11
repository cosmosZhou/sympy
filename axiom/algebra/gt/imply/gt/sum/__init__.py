from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)
    print('need to prove', limits, 'are nonemptysets')
    return Greater(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Greater(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq << algebra.all_gt.imply.gt.sum.apply(Eq[-1])

    


if __name__ == '__main__':
    run()

from . import mul
# created on 2019-07-24
# updated on 2022-04-01
