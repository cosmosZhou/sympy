from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Min >= Expr)
    first = args[:index]
    second = args[index:]
    
    return GreaterEqual(Min(*first), x), GreaterEqual(Min(*second), x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(Min(y, z) >= x)

    Eq << algebra.ge_min.imply.ge.apply(Eq[0], index=0)

    Eq << algebra.ge_min.imply.ge.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()