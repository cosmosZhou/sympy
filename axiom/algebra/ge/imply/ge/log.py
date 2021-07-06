from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert rhs > 0

    return GreaterEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(positive=True)
    Eq << apply(GreaterEqual(x, y))

    Eq << Eq[1].this.apply(algebra.ge.given.is_nonnegative)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.log)

    Eq.is_nonnegative = Eq[0] / y - 1

    t = Symbol.t(nonnegative=True)
    Eq << GreaterEqual(log(1 + t), 0, plausible=True)

    Eq << algebra.cond.imply.all.apply(Eq[-1], t)

    t = Eq[-1].variable
    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << Eq[-1].subs(t, Eq.is_nonnegative.lhs)
    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq.is_nonnegative, Eq[-1])


if __name__ == '__main__':
    run()