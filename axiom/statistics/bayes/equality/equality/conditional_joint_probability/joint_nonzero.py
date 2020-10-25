
from sympy.core.relational import Equality, Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from axiom import algebre


# given: P(x | z) = P(x) and P(y | z) = P(y)
# imply: P(x & y) | P(z) = P(x & y)
@plausible
def apply(*given):
    given_x, given_y, unequality = given
    assert given_x.is_Equality
    assert given_y.is_Equality
    assert unequality.is_Unequality
    assert unequality.rhs.is_zero
    
    x = given_x.rhs
    y = given_y.rhs
    assert unequality.lhs.arg == x.as_boolean() & y.as_boolean() 
    
    eq = given_x.lhs
    assert eq.is_Conditioned
    _x, z = eq.args

    eq = given_y.lhs
    assert eq.is_Conditioned
    _y, _z = eq.args
    
    assert x == _x
    assert y == _y
    assert z == _z
    
    assert x.is_random and y.is_random and z.is_random
    return Equality(P(x, y, given=z), P(x, y), given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
        
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(P(x, y), 0))
    
    Eq << bayes.inequality.et.apply(Eq[2]).split()
    
    Eq << bayes.equality.equality.conditional_joint_probability.nonzero.apply(Eq[0], Eq[1], Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
