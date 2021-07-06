from util import *


@apply
def apply(is_positive, gt):
    x = is_positive.of(Expr > 0)
    if x is None:
        is_positive, gt = gt, is_positive
        x = is_positive.of(Expr > 0)
        
    lhs, rhs = gt.of(Greater)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(x > 0, a > b)

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[0])

    Eq << algebra.is_positive.gt.imply.gt.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()