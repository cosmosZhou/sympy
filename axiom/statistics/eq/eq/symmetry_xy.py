from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics, algebre


# given: x | y = x
# imply: y | x = y
@apply
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
 
    Eq << apply(given, Unequal(P(x, y), 0))
    
    Eq << statistics.is_nonzero.et.apply(Eq[1])
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << statistics.eq.eq.symmetry.apply(Eq[0], Eq[-2])
    
if __name__ == '__main__':
    prove(__file__)
