from util import *



@apply
def apply(*given):
    x_less_than_a, y_less_than_b = given
    abs_x, a = x_less_than_a.of(Less)
    abs_y, b = y_less_than_b.of(Less)

    x = abs_x.of(Abs)
    y = abs_y.of(Abs)

    return Less(abs(x + y), a + b)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(abs(x) < a, abs(y) < b)

    Eq << algebra.lt.given.cond.split.abs.apply(Eq[-1])

    Eq << algebra.lt.imply.cond.split.abs.apply(Eq[0])

    Eq << algebra.lt.imply.cond.split.abs.apply(Eq[1])

    Eq <<= Eq[-4] + Eq[-2], Eq[-3] + Eq[-1]


if __name__ == '__main__':
    run()
