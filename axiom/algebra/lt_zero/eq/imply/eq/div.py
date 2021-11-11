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

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) < 0, Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << algebra.lt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[-1], Eq[1])
    Eq << Eq[2].this.rhs.apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2020-01-16
# updated on 2020-01-16
