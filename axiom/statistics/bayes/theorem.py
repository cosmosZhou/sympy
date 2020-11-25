
from sympy.core.relational import Equality, Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P, Probability
from sympy.stats.rv import pspace
from sympy.concrete.expr_with_limits import ForAll
from sympy.logic.boolalg import And


# given: P(x) ! =0
# imply: P(x, y) = P(y | x) P(x) 
@plausible
def apply(self, *given):
    assert self.is_Probability
    if len(given) == 1:
        given = given[0]
        marginal_prob = self.marginalize(given)
    
        expr = marginal_prob.arg
        if expr.is_Conditioned and self.arg.is_Conditioned:
            given_probability = self.func(given, given=expr.rhs)
        else:
            given_probability = self.func(given)
        
        given_marginal_prob = self.func(expr, given=given)
        assert given_marginal_prob.arg.is_Conditioned
        
        if given_marginal_prob.arg.rhs.is_And:
            given_additions = given_marginal_prob.arg.rhs._argset - {given.as_boolean()}                    
            inequality = Unequal(self.func(given_probability.arg, given=And(*given_additions)), 0)
        else:
            inequality = Unequal(given_probability, 0)
        
        return ForAll[given: inequality](Equality(self, given_probability * given_marginal_prob))
    else:
        from sympy import S
        marginal_prob = self
        cond = S.true
        for g in given:
            marginal_prob = marginal_prob.marginalize(g)
            cond &= g.as_boolean()            
        
        expr = marginal_prob.arg
        if expr.is_Conditioned and self.arg.is_Conditioned:
            given_probability = self.func(cond, given=expr.rhs)
        else:
            given_probability = self.func(cond)
        
        given_marginal_prob = self.func(expr, given=cond)
        assert given_marginal_prob.arg.is_Conditioned
        
        if given_marginal_prob.arg.rhs.is_And:
            given_additions = given_marginal_prob.arg.rhs._argset - cond._argset                    
            inequality = Unequal(self.func(given_probability.arg, given=And(*given_additions)), 0)
        else:
            inequality = Unequal(given_probability, 0)
        
        return ForAll[given: inequality](Equality(self, given_probability * given_marginal_prob))

    

@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)    
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Probability(x, y), y)


if __name__ == '__main__':
    prove(__file__)
