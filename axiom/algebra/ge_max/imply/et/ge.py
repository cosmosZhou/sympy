from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(GreaterEqual[Expr, Max])
    first = args[:index]
    second = args[index:]

    return GreaterEqual(x, Max(*first)), GreaterEqual(x, Max(*second))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << algebra.ge_max.imply.ge.apply(Eq[0], index=0)

    Eq << algebra.ge_max.imply.ge.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-06-06
# updated on 2019-06-06
