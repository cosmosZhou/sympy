from util import *


@apply
def apply(x):
    return log(x) <= x - 1


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x = Symbol.x(real=True)
    Eq << apply(x)

    Eq << Eq[0] - x

    Eq << algebra.cond.given.all.apply(Eq[-1])

    Eq << algebra.all.given.et.apply(Eq[-1], cond=x >= 1)

    

    x0 = Symbol.x0(domain=Interval(0, 1, left_open=True, right_open=True))
    x1 = Symbol.x1(domain=Interval(1, oo))
    Eq <<= algebra.all.given.cond.subs.apply(Eq[-2], x, x0), algebra.all.given.cond.subs.apply(Eq[-1], x, x1)

    Eq.is_positive, Eq.is_nonpositive = Greater(Derivative[x0](Eq[-2].lhs), 0, plausible=True), LessEqual(Derivative[x1](Eq[-1].lhs), 0, plausible=True)

    Eq << Eq.is_positive.this.lhs.doit()

    Eq << Eq.is_nonpositive.this.lhs.doit()

    Eq <<= Eq[-2] * x0, Eq[-1] * x1

    Eq <<= Eq[-2].this.lhs.apply(algebra.mul.to.add), Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << calculus.is_positive.imply.lt.monotony.apply(Eq.is_positive)

    Eq << algebra.lt.imply.le.relax.apply(Eq[-1])

    Eq << calculus.is_nonpositive.imply.le.monotony.apply(Eq.is_nonpositive)


if __name__ == '__main__':
    run()