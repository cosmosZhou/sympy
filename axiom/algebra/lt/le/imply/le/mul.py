from util import *


@apply
def apply(lt, le):
    a, b = lt.of(Less)
    x, y = le.of(LessEqual)
    z = b - a
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(a < b, x <= y)

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.le.imply.le.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()