from util import *



@apply
def apply(given):
    expr = given.of(Unequal[0])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << algebra.eq.imply.ne_zero.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-01-27
# updated on 2020-01-27
