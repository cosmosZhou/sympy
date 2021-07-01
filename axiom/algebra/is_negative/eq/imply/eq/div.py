from util import *


@apply
def apply(is_negative, eq):
    if is_negative.is_Equal:
        eq, is_negative = is_negative, eq

    x = is_negative.of(Expr < 0)
    lhs, rhs = eq.of(Equal)

    return Equal(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    Eq << apply(f(x) < 0, Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << algebra.is_negative.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.is_nonzero.eq.imply.eq.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()