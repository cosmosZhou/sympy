from util import *


@apply
def apply(given):
    equal, notcontains = given.of(Or)

    x, b = equal.of(Equal)
    _x, ab = notcontains.of(NotContains)
    assert x == _x
    a, b = ab.of(Interval)
    assert not ab.right_open

    ab = ab.copy(right_open=True)
    return NotContains(x, ab)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Equal(x, b) | NotContains(x, Interval(a, b)))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()

