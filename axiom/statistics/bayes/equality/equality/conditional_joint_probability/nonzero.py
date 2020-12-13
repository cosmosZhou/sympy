
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
    assert unequality.lhs.arg.lhs in {x, y} 
    
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
    return Equality(P(x, y, given=z), P(x, y))


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
        
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(P(y), 0))
    
    Eq << bayes.equality.equality.product.apply(Eq[0])
    
    Eq.bayes_yz = bayes.equality.equality.product.apply(Eq[1])
    
    Eq.bayes_xyz = bayes.corollary.apply(Eq[0].domain_definition(), var=P(x, y))
    
    Eq << Eq[2].subs(Eq[1].reversed)
    
    Eq.given_addition = bayes.equality.equality.given_addition.condition_probability.apply(Eq[0], Eq[-1])
    
    Eq << bayes.is_nonzero.is_nonzero.joint.apply(Eq[-1])
    
    Eq << bayes.corollary.apply(Eq[-1], var=x)
    
    Eq << Eq.bayes_xyz.subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.bayes_yz)
    
    Eq << algebre.is_nonzero.equality.imply.equality.scalar.apply(Eq[-1], Eq[0].domain_definition())
    
    Eq << Eq[-1].subs(Eq.given_addition)
    
    Eq << bayes.corollary.apply(Eq[2], var=x)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)
