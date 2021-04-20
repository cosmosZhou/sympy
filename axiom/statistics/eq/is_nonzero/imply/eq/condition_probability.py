from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import algebra, statistics


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(*given):
    equality, unequal = given
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    assert unequal.lhs.arg.is_Conditioned
    z, _y = unequal.lhs.arg.args
        
    assert equality.is_Equal
    lhs, rhs = equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs
    
    if _y != y:
        _y, z = z, _y
        
    assert _y == y    
    
    return Equal(x | y & z, x | z)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equal(x | y, x), Unequal(P(z | y), 0))
    
    Eq << statistics.bayes.theorem.apply(P(x | y, z), z)
    
    Eq << algebra.forall.imply.ou.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])
    
    Eq << statistics.is_nonzero.imply.is_nonzero.marginal.apply(Eq[1])
    
    Eq << statistics.bayes.corollary.apply(Eq[-1], var=x)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[-1], Eq[-3])
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove()
