from util import *


@apply
def apply(given):
    lhs, *limits = given.of(Any[Unequal[0]])
    shape = given.limits_shape
    
    return Unequal(Lamda(lhs, *limits), ZeroMatrix(*shape, *lhs.shape))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:n](Unequal(f(i), 0)))

    Eq << ~Eq[1]

    Eq << algebra.lamda_is_zero.imply.all_is_zero.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-01-01
