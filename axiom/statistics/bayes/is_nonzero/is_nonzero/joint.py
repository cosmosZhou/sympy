from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics


# given: P(x | y) != 0
# imply: P(x, y) != 0
@apply(imply=True)
def apply(given):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    eq = given.lhs.arg
    assert eq.is_Conditioned     
    return Unequal(P(eq.lhs, eq.rhs), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x | y), 0))
    
    Eq << Eq[0].domain_definition()
    
    Eq << statistics.bayes.corollary.apply(Eq[-1], var=x)
    
    Eq << Eq[0] * Eq[2]
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
if __name__ == '__main__':
    prove(__file__)
