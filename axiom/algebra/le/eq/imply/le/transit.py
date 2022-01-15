from util import *


@apply
def apply(le, eq):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return LessEqual(*swap(LessEqual, le, eq))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    #Eq << apply(a <= x, Equal(b, a))
    #Eq << apply(a <= x, Equal(a, b))
    Eq << apply(a <= x, Equal(x, b))

    #Eq << apply(a <= x, Equal(b, x))
    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)


if __name__ == '__main__':
    run()
# created on 2019-10-24
