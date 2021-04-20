from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import algebra, statistics


# given: P(x | z) = P(x) and P(y | z) = P(y)
# imply: P(x & y) | P(z) = P(x & y)
@apply
def apply(*given):
    given_x, given_y, unequality = given
    assert given_x.is_Equal
    assert given_y.is_Equal
    assert unequality.is_Unequal
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
    return Equal(P(x, y, given=z), P(x, y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
        
    Eq << apply(x.is_independent_of(z), y.is_independent_of(z), Unequal(P(x, y), 0))
    
    Eq << statistics.is_nonzero.imply.et.apply(Eq[2])
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << statistics.eq.eq.is_nonzero.imply.eq.nonzero.apply(Eq[0], Eq[1], Eq[-1])
    
if __name__ == '__main__':
    prove()
