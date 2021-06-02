from util import *
import axiom


@apply
def apply(*given):
    greater_than, less_than = given
    x, a = greater_than.of(GreaterEqual)
    y, b = less_than.of(LessEqual)

    return LessEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x >= a, y <= b)

    Eq << Eq[1].reversed

    Eq << algebra.ge.ge.imply.is_nonnegative.apply(Eq[0], Eq[-1])
    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()
