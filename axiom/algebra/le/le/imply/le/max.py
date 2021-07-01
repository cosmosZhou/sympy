from util import *


@apply
def apply(x_less_than_a, y_less_than_a):
    x, a = x_less_than_a.of(LessEqual)
    y, _a = y_less_than_a.of(LessEqual)
    assert a == _a
    return LessEqual(Max(x, y), a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x <= a, y <= a)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=x >= y)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq.ou = algebra.ou.imply.ou.invert.apply(Eq[-2])

    Eq << Eq[1].apply(algebra.cond.imply.et.ou, cond=x >= y)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.ou.imply.ou.invert.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)


if __name__ == '__main__':
    run()
