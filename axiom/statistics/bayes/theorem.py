
from sympy.core.relational import Equality, Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from sympy.stats.rv import pspace


# given: P(x) ! =0
# imply: P(x, y) = P(y | x) P(x) 
@plausible
def apply(given, var):
    assert given.is_Unequality
    x_probability, zero = given.args
    
    assert zero.is_zero
    eq = x_probability.arg    
    if eq.is_Equality:
        x, _x = eq.args
        assert x.is_random and _x == pspace(x).symbol
        
        if var.is_Probability:
            joint_probability = var
            marginal_probability = joint_probability.marginalize(x)
            if marginal_probability is None:
                var = joint_probability.arg
                joint_probability = P(joint_probability.arg, x)                  
            else:
                var = marginal_probability.arg
            
            assert not var.is_Conditioned        
            return Equality(joint_probability, P(var | x) * P(x), given=given)
        else:
            return Equality(P(x, var), P(var | x) * P(x), given=given)
    elif eq.is_Conditioned:
        x, _x = eq.lhs.args
        assert x.is_random and _x == pspace(x).symbol
        
        assert var.is_Probability
        joint_probability = var
        var = joint_probability.marginalize(x).arg
        assert var.is_Conditioned    
        assert var.rhs == eq.rhs 
        return Equality(joint_probability, P(var | x) * P(x, given=eq.rhs), given=given)
    else:
        assert eq.is_And       
        assert var.is_random and var.is_symbol
        assert var.as_boolean() not in eq._argset 
        return Equality(P(eq, var), P(var | eq) * P(eq), given=given)
        
    

@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)    
    y = Symbol.y(real=True, random=True)
    
    given = Unequal(P(x), 0)
    
    Eq << apply(given, y)
    
    Eq << Eq[-1].lhs.bayes_theorem(x)
    
    Eq << Eq[-1].as_Or()
    
    Eq << (Eq[-1] & Eq[0]).split()


if __name__ == '__main__':
    prove(__file__)
