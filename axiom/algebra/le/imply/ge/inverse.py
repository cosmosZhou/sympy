from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    assert x > 0

    return GreaterEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, positive=True)
    a = Symbol.a(real=True)
    Eq << apply(x <= a)

    Eq << algebra.le.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[-1])

    Eq << algebra.is_positive.le.imply.le.mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * x
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()