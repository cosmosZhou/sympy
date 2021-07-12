from util import *


@apply
def apply(given):
    (fx, (x, n)), (_x, a, b) = given.of(All[Derivative > 0])
    assert n == 1
    assert x == _x
    
    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    domain = Interval(a, b)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << algebra.cond.given.suffice.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.all_et.limits_cond, simplify=None)

    Eq << (a >= b).this.apply(sets.ge.imply.is_emptyset, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=a < b)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])
    Eq << Eq[-1].this.rhs.apply(calculus.lt.all_is_positive.imply.all_gt.monotony.right_close)


if __name__ == '__main__':
    run()