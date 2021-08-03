from util import *


@apply
def apply(given):
    x, n = given.of(Equal[Expr ** Expr, 0])
    assert n.is_integer and n > 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol.x(complex=True, given=True)
    Eq << apply(Equal(x ** n, 0))

    Eq << algebra.eq.imply.eq.pow.apply(Eq[1], exp=n)

    


if __name__ == '__main__':
    run()