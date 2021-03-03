from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, geometry, calculus, sets


@apply
def apply(x):
    i = S.ImaginaryUnit
    return Equality(E ** (i * x), cos(x) + i * sin(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)
    
    i = S.ImaginaryUnit
    Eq << calculus.series.maclaurin.exp.apply(i * x)
    
    n = Eq[-1].rhs.variable
    
    Eq << Eq[-1].this.rhs.bisect((-1) ** n > 0)
    
    Eq << Eq[-1].this.rhs.args[0].limits[0][1].apply(sets.complement.astype.conditionset)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebre.sum.even)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebre.sum.odd)
    
    Eq << Eq[-1].this.rhs.args[0].function.expand()
    
    Eq.expand = Eq[-1].this.rhs.args[0].function.expand()
    
    Eq << cos(x).this.definition
    
    Eq << sin(x).this.definition
    
    Eq << Eq[-2] + i * Eq[-1]
    
    Eq << Eq[-1].this.rhs.args[0].args[1].function.expand()
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.expand, Eq[-1])
    
    


if __name__ == '__main__':
    prove(__file__)

