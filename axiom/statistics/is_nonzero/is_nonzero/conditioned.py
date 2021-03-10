from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import algebre, statistics


# given: P(x, y) != 0
# imply: P(x | y) != 0
@apply
def apply(given, wrt):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
        
    probability = given.lhs
    p = probability.marginalize(wrt)
    
    return Unequal(P(p.arg | wrt), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x, y), 0), y)
    
    Eq << statistics.is_nonzero.et.apply(Eq[0]).split()
    
    Eq << statistics.bayes.corollary.apply(Eq[-1], var=Eq[0].lhs)
    
    Eq << Eq[0].subs(Eq[-1])
    
    Eq << algebre.is_nonzero.unequal.imply.unequal.scalar.apply(Eq[-3], Eq[-1]) 
    
    
if __name__ == '__main__':
    prove(__file__)
