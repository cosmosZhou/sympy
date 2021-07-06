from util import *


@apply
def apply(x_less_than_a, y_less_than_b):
    abs_x, a = x_less_than_a.of(Less)
    abs_y, b = y_less_than_b.of(Less)

    x = abs_x.of(Abs)
    y = abs_y.of(Abs)

    return Less(abs(x * y), a * b)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(abs(x) < a, abs(y) < b)

    Eq << algebra.lt.lt.imply.lt.mul.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.abs)


if __name__ == '__main__':
    run()
