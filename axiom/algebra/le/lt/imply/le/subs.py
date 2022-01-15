from util import *


@apply
def apply(le, lt):
    from axiom.algebra.eq.le.imply.le.subs import ratsimp
    assert le.is_LessEqual
    assert lt.is_Less

    lhs, rhs, k = ratsimp(le, lt)
    assert k >= 0
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra
    t, x, y, b = Symbol(real=True)
    k = Symbol(real=True, nonnegative=True)

    Eq << apply(y <= x * k + b, x < t)

    Eq << algebra.lt.imply.le.mul.apply(Eq[1], k)

    Eq << Eq[-1] + b

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
# created on 2019-11-25
