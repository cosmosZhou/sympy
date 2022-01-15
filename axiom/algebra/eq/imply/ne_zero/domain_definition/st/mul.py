from util import *


@apply
def apply(given):
    (num, den), rhs = given.of(Equal[Expr / Expr, Expr])
    return Unequal(den, 0)


@prove(provable=False)
def prove(Eq):
    a, c, b = Symbol(complex=True)
    Eq << apply(Equal(a / b, c))


if __name__ == '__main__':
    run()
# created on 2019-04-14
