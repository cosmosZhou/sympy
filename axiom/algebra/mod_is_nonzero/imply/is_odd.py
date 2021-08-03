from util import *


@apply
def apply(given):
    n = given.of(Unequal[Expr % 2, 0])
    return Equal(n % 2, 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << sets.imply.contains.mod.apply(n % 2)

    Eq << sets.contains.imply.ou.split.interval.apply(Eq[-1])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
