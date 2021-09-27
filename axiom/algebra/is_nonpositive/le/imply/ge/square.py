from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, _x = le.of(LessEqual)
    assert x == _x
    return GreaterEqual(y ** 2, x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.le.imply.is_nonpositive.apply(Eq[1])

    Eq << algebra.is_nonpositive.is_nonpositive.imply.is_nonnegative.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.apply(algebra.ge.transposition, lhs=0)


if __name__ == '__main__':
    run()