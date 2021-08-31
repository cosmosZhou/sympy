from util import *


@apply
def apply(gt, index=0):
    x, args = gt.of(Greater[Expr, Max])
    first = args[:index]
    second = args[:index]

    return Greater(x, Max(*first)), GreaterEqual(x, Max(*second))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Max(y, z))

    Eq << algebra.gt_max.imply.gt.apply(Eq[0], index=0)
    Eq << algebra.gt_max.imply.gt.apply(Eq[0], index=1)



if __name__ == '__main__':
    run()
