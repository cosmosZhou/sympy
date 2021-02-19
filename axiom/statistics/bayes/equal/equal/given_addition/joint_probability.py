
from sympy.core.relational import Equality, Unequal

from axiom.utility import prove, apply
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(*given):
    equality, unequal = given
    if equality.is_Unequality:
        equality, unequal = unequal, equality
    assert unequal.is_Unequality
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    _y, z = unequal.lhs.arg.args
        
    assert equality.is_Equality
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
        return Equality(x | y & z, x | z)
    else:
        return Equality(P(x, given=y & z), P(x, given=z))


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y, x), Unequal(P(y, z), 0))
    
    Eq << bayes.is_nonzero.is_nonzero.conditioned.apply(Eq[1], y)
    
    Eq << bayes.equal.equal.given_addition.condition_probability.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)
