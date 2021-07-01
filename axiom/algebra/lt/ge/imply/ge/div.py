from util import *


@apply
def apply(lt, ge):
    if ge.is_Less:
        lt, ge = ge, lt
    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(x < y, a * (y - x) >= b)

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.ge.imply.ge.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()