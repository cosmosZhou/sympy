
from sympy.core.relational import Equality

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics


# given: x | y = x
# imply: P(x, y) = P(x) P(y)
@plausible
def apply(given):    
    assert given.is_Equality
    lhs, rhs = given.args

    assert lhs.is_Conditioned
    
    x, y = lhs.args
    
    assert x == rhs
    
    return Equality(P(x, y), P(x) * P(y))


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    given = Equality(x | y, x)
    
    Eq << apply(given)
    
    Eq << statistics.bayes.corollary.apply(Eq[0].lhs.domain_definition(), var=x)
    
    Eq << Eq[-1].subs(Eq[0].probability())
    

if __name__ == '__main__':
    prove(__file__)
