from util import *


@apply
def apply(ge):
    x, a = ge.of(Greater)
    assert a > 0

    return Less(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    a = Symbol.a(real=True, positive=True)
    Eq << apply(x > a)

    Eq << algebra.gt.imply.is_positive.transit.apply(Eq[0])

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[-1])

    Eq << algebra.is_positive.gt.imply.gt.mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * a


if __name__ == '__main__':
    run()