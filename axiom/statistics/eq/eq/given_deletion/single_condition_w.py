from sympy import *
from sympy.stats.symbolic_probability import Probability as P
from axiom.utility import prove, apply
from axiom import algebre, statistics, calculus
from sympy.stats.rv import pspace

# given: x | y & z = x
# imply: x | y = x
@apply
def apply(given, wrt=None):    
        
    assert given.is_Equality
    lhs, rhs = given.args
    assert lhs.is_Conditioned
    x, yzw = lhs.args
    assert rhs.is_Conditioned
    _x, w = rhs.args
    assert x == _x

    assert w in yzw.args
    args = [*yzw.args]
    args.remove(w)
    y, z = args
#     assert w in yzw._argset
#     y, z = {*yzw.args} - {w}
    
    if wrt is not None:
        if y.is_Equality:
            y = y.lhs
        if z.is_Equality:
            z = z.lhs
            
        assert wrt in {y, z}
        return Equality(x | wrt.as_boolean() & w, x | w)
    return Equality(x | y & w, x | w)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    w = Symbol.w(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean() & w.as_boolean(), x | w), wrt=y)
    
    Eq << Eq[0].domain_definition()
    
    Eq.xyz_nonzero, Eq.w_nonzero = algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << statistics.is_nonzero.et.apply(Eq.xyz_nonzero)
    
    Eq.y_nonzero, Eq.z_nonzero = algebre.et.imply.cond.apply(Eq[-1], index=Slice[1:3])
    
    Eq.xy_probability = statistics.bayes.corollary.apply(Eq.y_nonzero, var=x | w)
    
    Eq << statistics.is_nonzero.is_nonzero.conditioned.apply(Eq.xyz_nonzero, wrt=w)
    
    Eq << statistics.bayes.theorem.apply(P(x | w, y, z), y, z)
    
    Eq << algebre.forall.imply.ou.rewrite.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq <<= statistics.total_probability_theorem.apply(Eq[-1].lhs, z), \
        statistics.total_probability_theorem.apply(Eq[-1].rhs.args[0], z), \
        calculus.eq.imply.eq.integrate.apply(Eq[-1], (pspace(z).symbol,))
    
    Eq << Eq[-3].subs(Eq.xy_probability)
    
    Eq << Eq[-1].subs(Eq[-2]) 
    
    Eq << Eq[-1].subs(Eq[-4])
    
    Eq << algebre.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq.y_nonzero)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

