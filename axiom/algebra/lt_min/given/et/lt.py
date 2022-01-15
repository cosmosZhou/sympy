from util import *


@apply
def apply(lt, index=-1):
    x, args = lt.of(Less[Expr, Min])
    first = args[:index]
    second = args[index:]

    return x < Min(*first), x < Min(*second)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x < Min(y, z))

    Eq << algebra.lt.lt.imply.lt.min.apply(Eq[1], Eq[2])

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
