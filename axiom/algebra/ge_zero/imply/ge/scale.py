from util import *


@apply
def apply(given, t):
    x = given.of(Expr >= 0)
    assert t >= 1
    return GreaterEqual(t * x, x)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(real=True, given=True)
    t = Symbol(integer=True, positive=True, odd=True)
    Eq << apply(a >= 0, t)

    Eq << GreaterEqual(t - 1, 0, plausible=True)

    Eq << algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << algebra.ge_zero.imply.ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-14
