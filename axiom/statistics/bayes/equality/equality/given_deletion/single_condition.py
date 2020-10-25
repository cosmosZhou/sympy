
from sympy.core.relational import Equality

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from axiom.statistics import bayes
from axiom import algebre
from sympy.stats.rv import pspace


# given: x | y & z = x
# imply: x | y = x
@plausible
def apply(given, wrt=None):    
        
    assert given.is_Equality
    lhs, rhs = given.args
    assert lhs.is_Conditioned
    x, yz = lhs.args
    assert x == rhs

    y, z = yz.args    
    
    if wrt is not None:
        if y.is_Equality:
            y = y.lhs
        if z.is_Equality:
            z = z.lhs
            
        assert wrt in {y, z}
        return Equality(x | wrt, x, given=given)
    return Equality(x | y, x, given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean(), x))
    
    Eq << Eq[0].domain_definition()
    
    Eq.y_nonzero, Eq.z_nonzero = bayes.inequality.et.apply(Eq[-1]).split()
    
    Eq.xy_probability = bayes.theorem.apply(Eq.y_nonzero, var=x)
    
    Eq << bayes.theorem.apply(Eq[2], var=x)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq <<= Eq[-1].lhs.total_probability_theorem(z), Eq[-1].rhs.args[0].total_probability_theorem(z), Eq[-1].integral((pspace(z).symbol,))
    
    Eq << Eq[-3].subs(Eq.xy_probability)
    
    Eq << Eq[-1].subs(Eq[-2]) 
    
    Eq << Eq[-1].subs(Eq[-4])
    
    Eq << algebre.scalar.inequality.equality.apply(Eq[-1], Eq.y_nonzero)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

