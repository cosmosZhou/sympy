from util import *
import axiom



@apply
def apply(given):
    expr, one = given.of(Unequal)
    if one != 1:
        expr, one = one, expr
    assert one == 1

    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)

    Eq << apply(Unequal(n % 2, 1))

    Eq << sets.imply.contains.mod.apply(n % 2)

    Eq << sets.contains.imply.ou.split.interval.apply(Eq[-1])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
