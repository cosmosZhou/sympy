from axiom.utility import prove, apply
from sympy import *
from sympy.stats.symbolic_probability import Probability as P, Probability
from sympy.stats.rv import pspace


# given: P(x) ! =0
# imply: P(x, y) = P(y | x) P(x) 
@apply
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
        
        return ForAll[given: inequality](Equal(self, given_probability * given_marginal_prob))
    else:
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
        
        return ForAll[given: inequality](Equal(self, given_probability * given_marginal_prob))
    

@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True, random=True)    
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Probability(x, y), y)


if __name__ == '__main__':
    prove()
