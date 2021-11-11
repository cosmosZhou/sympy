from util import *


@apply
def apply(ge, eq):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return GreaterEqual(*swap(GreaterEqual, ge, eq))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    #Eq << apply(b >= x, Equal(x, a))
    Eq << apply(b >= x, Equal(a, b))

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.ge.simplify.common_terms)


if __name__ == '__main__':
    run()
# created on 2019-05-15
# updated on 2019-05-15
