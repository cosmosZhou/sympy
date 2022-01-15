from util import *


@apply
def apply(lt, index=-1):
    x, args = lt.of(Less[Expr, Min])
    first = args[:index]
    second = args[index:]

    return Less(x, Min(*first)), Less(x, Min(*second))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x < Min(y, z))

    Eq << algebra.lt_min.imply.lt.apply(Eq[0], index=0)

    Eq << algebra.lt_min.imply.lt.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2020-01-12
