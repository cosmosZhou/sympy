from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << algebra.is_even.imply.any.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.eq.pow, base=-1)


if __name__ == '__main__':
    run()

# created on 2019-10-10
# updated on 2019-10-10
