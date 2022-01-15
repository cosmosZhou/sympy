from util import *


@apply
def apply(given):
    lhs, *limits = given.of(Equal[Lamda, ZeroMatrix])

    return All(Equal(lhs, ZeroMatrix(*lhs.shape)), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Equal(Lamda[i:n](f(i)), ZeroMatrix(n)))

    j = Symbol(domain=Range(n))
    Eq << Eq[0][j]

    Eq << algebra.cond.imply.all.domain_defined.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
