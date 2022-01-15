from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Equal[0]])
    shape = given.limits_shape
    
    return Equal(Lamda(lhs, *limits), ZeroMatrix(*shape, *lhs.shape))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:n](Equal(f(i), 0)))

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[1], j)

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], i, j)


if __name__ == '__main__':
    run()
# created on 2022-01-01
