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

    Eq << algebra.eq.imply.is_nonzero.apply(Eq[1])


if __name__ == '__main__':
    run()
