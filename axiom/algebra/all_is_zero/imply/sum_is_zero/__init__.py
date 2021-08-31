from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Equal[0]])

    return Equal(Sum(lhs, *limits), 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply(All[i:n](Equal(f(i), 0)))
    
    Eq << algebra.all_eq.imply.eq.sum.apply(Eq[0])


if __name__ == '__main__':
    run()

from . import mul
