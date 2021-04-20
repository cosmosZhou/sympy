from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(*given):
    equality, unequal = given
    if equality.is_Unequal:
        equality, unequal = unequal, equality
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    _y, z = unequal.lhs.arg.args
        
    assert equality.is_Equal
    lhs, rhs = equality.args
    if lhs.is_Probability:
        assert rhs.is_Probability
        lhs = lhs.arg
        rhs = rhs.arg
        
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs
    
    if _y != y:
        _y, z = z, _y
        
    assert _y == y    
    
    if x.is_symbol:
        return Equal(x | y & z, x | z)
    else:
        return Equal(P(x, given=y & z), P(x, given=z))


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equal(x | y, x), Unequal(P(y, z), 0))
    
    Eq << statistics.is_nonzero.imply.is_nonzero.conditioned.apply(Eq[1], y)
    
    Eq << statistics.eq.is_nonzero.imply.eq.condition_probability.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove()
