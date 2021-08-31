from util import *


@apply
def apply(x_less_than_a, y_less_than_a):
    x, a = x_less_than_a.of(Less)
    y, _a = y_less_than_a.of(Less)
    assert a == _a
    return Less(Max(x, y), a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, y = Symbol(real=True, given=True)

    Eq << apply(x < a, y < a)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True)


if __name__ == '__main__':
    run()
