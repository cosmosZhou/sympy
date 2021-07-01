from util import *


@apply
def apply(*given):     
    from axiom.algebra.lt.eq.imply.lt.transit import swap    
    return GreaterEqual(*swap(GreaterEqual, *given))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    #Eq << apply(b >= x, Equal(x, a))
    Eq << apply(b >= x, Equal(a, b))

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.ge.simplify.common_terms)


if __name__ == '__main__':
    run()
