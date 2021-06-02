from util import *



@apply
def apply(given, lower):
    assert given.is_GreaterEqual
    lhs, rhs = given.args
    assert rhs >= lower
    return GreaterEqual(lhs, lower)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    z = Symbol.z(domain=Interval(-oo, y))
    Eq << apply(x >= y, z)

    Eq << GreaterEqual(y, z, plausible=True)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
