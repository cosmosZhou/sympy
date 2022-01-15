from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(Any[Unequal])
    return Unequal(Lamda(lhs, *limits), Lamda(rhs, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Any[i:n](Unequal(f(i), g(i))))

    Eq << ~Eq[1]

    Eq << algebra.eq.imply.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.lamda)

    Eq << algebra.lamda_is_zero.imply.all_is_zero.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(algebra.is_zero.imply.eq)

    Eq << ~Eq[-1]

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
