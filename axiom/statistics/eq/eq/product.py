from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics, algebra


# given: x | y = x
# imply: P(x, y) = P(x) P(y)
@apply
def apply(given):    
    assert given.is_Equal
    lhs, rhs = given.args

    assert lhs.is_Conditioned
    
    x, y = lhs.args
    
    assert x == rhs
    
    return Equal(P(x, y), P(x) * P(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    given = Equal(x | y, x)
    
    Eq << apply(given)
    
    Eq << statistics.bayes.corollary.apply(Eq[0].lhs.domain_definition(), var=x)
    
    Eq << Eq[0].apply(statistics.eq.eq.probability, simplify=None)
    
    Eq << Eq[-2].subs(Eq[-1])
    

if __name__ == '__main__':
    prove()
