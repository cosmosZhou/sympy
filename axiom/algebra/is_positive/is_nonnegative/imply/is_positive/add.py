from util import *


@apply
def apply(is_positive, is_nonnegative):
    a = is_nonnegative.of(Expr >= 0)
    y = is_positive.of(Expr > 0)

    return Greater(a + y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    y = Symbol.y(real=True)
    Eq << apply(y > 0, a >= 0)

    Eq << algebra.ge.gt.imply.gt.add.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()