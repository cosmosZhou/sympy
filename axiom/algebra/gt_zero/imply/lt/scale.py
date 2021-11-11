from util import *


@apply
def apply(given, t):
    x = given.of(Expr > 0)
    assert t < 1
    return Less(t * x, x)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(real=True, given=True)
    t = Symbol(domain=Interval(-oo, 1, right_open=True))
    Eq << apply(a > 0, t)

    Eq << Less(t - 1, 0, plausible=True)

    Eq << algebra.gt_zero.lt_zero.imply.lt_zero.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << algebra.lt_zero.imply.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-14
# updated on 2019-08-14
