
from sympy.core.relational import Equality, Unequal

from axiom.utility import prove, apply
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes


# given: x | y = x
# imply: y | x = y
@apply(imply=True)
def apply(*given):
    given_equality, unequal = given
    assert unequal.is_Unequality
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
        
    assert given_equality.is_Equality
    lhs, rhs = given_equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs
    
    if y.is_Equality:
        y = y.lhs
    assert y.is_random and y.is_symbol
    return Equality(y | x, y)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    given = Equality(x | y, x)
 
    Eq << apply(given, Unequal(P(x), 0))
    
    Eq << bayes.equal.equal.product.apply(given)
    
    Eq << bayes.equal.equal.independence.apply(Eq[-1], Eq[1])
    
if __name__ == '__main__':
    prove(__file__)
