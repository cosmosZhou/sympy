from util import *


@apply
def apply(given):    
    x = given.of(Expr > 0)

    return Greater(x * x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    Eq << apply(x > 0)
    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[0], Eq[0])


if __name__ == '__main__':
    run()