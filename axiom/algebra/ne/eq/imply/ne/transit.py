from util import *


@apply
def apply(ne, eq):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return Unequal(*swap(Unequal, ne, eq))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    #Eq << apply(b > x, Equal(x, a))
    Eq << apply(Unequal(b, x), Equal(a, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(algebra.ne.simplify.common_terms)


if __name__ == '__main__':
    run()
# created on 2020-02-04
# updated on 2020-02-04
