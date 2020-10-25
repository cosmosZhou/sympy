from sympy.core.relational import  Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from axiom import algebre


# given: P(x, y) != 0
# imply: P(x | y) != 0
@plausible
def apply(given, wrt):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
        
    probability = given.lhs
    p = probability.marginalize(wrt)
    
    return Unequal(P(p.arg | wrt), 0, given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x, y), 0), y)
    
    Eq << bayes.inequality.et.apply(Eq[0]).split()
    
    Eq << bayes.theorem.apply(Eq[-1], var=Eq[0].lhs)
    
    Eq << Eq[0].subs(Eq[-1])
    
    Eq << algebre.scalar.inequality.inequality.apply(Eq[-3], Eq[-1]) 
    
    
if __name__ == '__main__':
    prove(__file__)
