from util import *


@apply
def apply(is_positive_x, lt):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = lt.of(Less)
    return Less(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a < b)

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[0])

    Eq << algebra.is_positive.lt.imply.lt.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()