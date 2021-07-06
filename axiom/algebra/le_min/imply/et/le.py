from util import *


@apply
def apply(le, index=-1):
    x, args = le.of(LessEqual[Expr, Min])
    first = args[:index]
    second = args[index:]
    
    return LessEqual(x, Min(*first)), LessEqual(x, Min(*second))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(x <= Min(y, z))

    Eq << algebra.le_min.imply.le.apply(Eq[0], index=0)

    Eq << algebra.le_min.imply.le.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()