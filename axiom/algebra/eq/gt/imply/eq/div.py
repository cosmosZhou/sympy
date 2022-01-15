from util import *


@apply
def apply(eq, gt):
    if gt.is_Equal:
        eq, gt = gt, eq

    x, y = gt.of(Greater)
    x -= y
    lhs, rhs = eq.of(Equal)

    return Equal(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) > g(x), Equal(g(x) * (f(x) - g(x)), h(x) * f(x) + x))

    Eq << algebra.gt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.eq.imply.eq.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-04-02
