from util import *


@apply
def apply(given, m):
    assert given.is_LessEqual
    lhs, rhs = given.args
    return LessEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    z = Symbol.z(real=True, given=True)
    Eq << apply(x <= y, z)

    Eq << Eq[0].reversed

    Eq << algebra.ge.imply.ge.min.apply(Eq[-1], z)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
