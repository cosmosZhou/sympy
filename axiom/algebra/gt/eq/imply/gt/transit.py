from util import *


@apply
def apply(gt, eq):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return Greater(*swap(Greater, gt, eq))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    #Eq << apply(b > x, Equal(x, a))
    Eq << apply(b > x, Equal(a, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(algebra.gt.simplify.common_terms)


if __name__ == '__main__':
    run()
# created on 2018-06-29
# updated on 2018-06-29
