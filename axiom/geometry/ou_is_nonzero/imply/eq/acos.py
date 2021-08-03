from util import *


@apply
def apply(ou, reverse=False):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    y = abs(y)
    lhs, rhs = acos(x / r), Piecewise((asin(y / r), x >= 0), (S.Pi - asin(y / r), True))
    if reverse:
        lhs, rhs = rhs, lhs
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Eq[-1].this.lhs.apply(geometry.acos.to.add.asin)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[1], cond=x >= 0)

    Eq <<= algebra.suffice.given.suffice.subs.bool.apply(Eq[-2]), algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()