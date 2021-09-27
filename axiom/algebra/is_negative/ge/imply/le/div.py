from util import *


@apply
def apply(is_negative, ge):
    x = is_negative.of(Expr < 0)
    #assert x.is_finite
    lhs, rhs = ge.of(GreaterEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a >= b)

    Eq << algebra.is_negative.imply.is_negative.div.apply(Eq[0])

    Eq << algebra.is_negative.ge.imply.le.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
