from util import *


@apply
def apply(*given):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return LessEqual(*swap(LessEqual, *given))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    #Eq << apply(a <= x, Equal(b, a))
    #Eq << apply(a <= x, Equal(a, b))
    Eq << apply(a <= x, Equal(x, b))

    #Eq << apply(a <= x, Equal(b, x))
    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)


if __name__ == '__main__':
    run()
