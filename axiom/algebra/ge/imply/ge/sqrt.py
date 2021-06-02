from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual[Basic ** 2, Basic ** 2])

    assert lhs.is_real
    assert rhs.is_real

    return GreaterEqual(abs(lhs), abs(rhs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(GreaterEqual(x * x, y * y))

    Eq << algebra.le.imply.le.sqrt.apply(Eq[0].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

