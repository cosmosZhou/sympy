
from sympy.core.relational import Equality

from axiom.utility import prove, apply
from sympy import Symbol
from axiom.statistics import bayes
from axiom import algebre, statistics
from sympy.stats.rv import pspace


# given: x | y & z = x
# imply: x | y = x
@apply
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
        return Equality(x | wrt, x)
    return Equality(x | y, x)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean(), x))
    
    Eq << Eq[0].domain_definition()
    
    Eq.y_nonzero, Eq.z_nonzero = bayes.is_nonzero.et.apply(Eq[-1]).split()
    
    Eq.xy_probability = bayes.corollary.apply(Eq.y_nonzero, var=x)
    
    Eq << bayes.corollary.apply(Eq[2], var=x)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq <<= statistics.total_probability_theorem.apply(Eq[-1].lhs, z), \
        statistics.total_probability_theorem.apply(Eq[-1].rhs.args[0], z), \
        algebre.equal.imply.equal.integrate.apply(Eq[-1], (pspace(z).symbol,))
    
    Eq << Eq[-3].subs(Eq.xy_probability)
    
    Eq << Eq[-1].subs(Eq[-2]) 
    
    Eq << Eq[-1].subs(Eq[-4])
    
    Eq << algebre.is_nonzero.equal.imply.equal.scalar.apply(Eq[-1], Eq.y_nonzero)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

