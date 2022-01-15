from util import *


@apply
def apply(le, le_neg):
    x, y = le.of(LessEqual)
    _x, _y = le_neg.of(LessEqual)
    assert x == -_x
    assert y == _y
    return abs(x) <= y


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= y, -x <= y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << algebra.le_zero.le_zero.imply.ge_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = algebra.le.imply.le.sqrt.apply(Eq[-1])

    Eq << algebra.le.ge.imply.ge.transit.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << algebra.ge_zero.imply.eq.abs.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-01-07
