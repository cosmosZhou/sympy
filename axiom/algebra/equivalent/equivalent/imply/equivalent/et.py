from util import *



@apply
def apply(*given):
    eq_ab, eq_xy = given
    a, b = eq_ab.of(Equivalent)
    x, y = eq_xy.of(Equivalent)
    return Equivalent(a & x, b & y)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Equivalent(a > 0, b > 0), Equivalent(x > 0, y > 0))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << algebra.equivalent.imply.suffice.apply(Eq[0])

    Eq << algebra.equivalent.imply.suffice.apply(Eq[1])

    Eq << algebra.suffice.suffice.imply.suffice.et.apply(Eq[-2], Eq[-1])

    Eq << algebra.equivalent.imply.necessary.apply(Eq[0])

    Eq << algebra.equivalent.imply.necessary.apply(Eq[1])

    Eq << algebra.necessary.necessary.imply.necessary.et.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()
