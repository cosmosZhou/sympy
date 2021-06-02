from util import *
import axiom



@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    b0, e0 = lhs.of(Pow)
    b1, e1 = rhs.of(Pow)
    assert e0.is_even
    assert e1.is_even

    e0 //= 2
    e1 //= 2

    return Greater(abs(b0 ** e0), abs(b1 ** e1))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(Greater(x * x, y * y))

    Eq << algebra.lt.imply.lt.sqrt.apply(Eq[0].reversed)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

