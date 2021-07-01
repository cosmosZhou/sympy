from util import *


@apply
def apply(given):
    x, y = given.of(Mul <= 0)
    return Or(And(x >= 0, y <= 0), And(x <= 0, y >= 0))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x * y <= 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(algebra.ou.imply.ou.invert, pivot=1)

    Eq << Eq[-1].this.args[1].apply(algebra.ou.imply.ou.invert, pivot=1)

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[1].apply(algebra.et.imply.ou)

    Eq << Eq[-1].this.args[-1].apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].apply(algebra.is_negative.is_negative.imply.is_positive)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
