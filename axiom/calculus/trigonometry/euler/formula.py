from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, geometry, calculus, sets


@apply
def apply(x):
    i = S.ImaginaryUnit
    return Equal(E ** (i * x), cos(x) + i * sin(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    i = S.ImaginaryUnit
    Eq << calculus.series.maclaurin.exp.apply(i * x)
    
    n = Eq[-1].rhs.variable
    
    Eq << Eq[-1].this.rhs.bisect(Equal(n % 2, 0))
    
    Eq << Eq[-1].this.rhs.args[0].limits[0][1].apply(sets.complement.to.conditionset)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.even)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.odd)
    
    Eq << Eq[-1].this.rhs.args[0].function.expand()
    
    Eq.expand = Eq[-1].this.rhs.args[0].function.expand()
    
    Eq << cos(x).this.definition
    
    Eq << sin(x).this.definition
    
    Eq << Eq[-2] + i * Eq[-1]
    
    Eq << Eq[-1].this.rhs.args[0].args[1].function.expand()
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.expand, Eq[-1])


if __name__ == '__main__':
    prove()

