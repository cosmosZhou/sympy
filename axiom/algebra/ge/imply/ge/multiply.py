from util import *
import axiom



@apply
def apply(given, factor):
    lhs, rhs = given.of(GreaterEqual)

    assert factor >= 0

    return GreaterEqual(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    k = Symbol.k(real=True, given=True, nonnegative=True)

    Eq << apply(GreaterEqual(x, y), k)

    Eq << GreaterEqual(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.is_nonnegative.imply.ge.apply(Eq[-1])


if __name__ == '__main__':
    run()

