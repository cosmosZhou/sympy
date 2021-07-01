from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    
    return Equal(Max(a, b), a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piecewise)
    Eq <<= Eq[0] & Eq[-1]
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()