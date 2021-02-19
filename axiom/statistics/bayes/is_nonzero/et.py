
from sympy.core.relational import Unequal

from axiom.utility import prove, apply
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from sympy.logic.boolalg import And
from axiom import algebre, statistics


# given: P(x, y) != 0
# imply: P(y) != 0
@apply
def apply(given, wrt=None):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    
    eqs = given.lhs.arg
    assert eqs.is_And
    if wrt is not None:
        lhs, rhs = [], []
        for eq in eqs.args:
            if eq.lhs in wrt:
                rhs.append(eq)
            else:
                lhs.append(eq)
        lhs = And(*lhs)
        rhs = And(*rhs)
        return And(Unequal(P(lhs), 0), Unequal(P(rhs), 0))            
    else:
        return And(*[Unequal(P(eq), 0) for eq in eqs.args])


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x, y), 0))
    
    Eq.x_marginal_probability, Eq.y_marginal_probability = statistics.total_probability_theorem.apply(P(x, y), y), statistics.total_probability_theorem.apply(P(x, y), x)
    
    _y = Eq.x_marginal_probability.lhs.variable
    _x = Eq.y_marginal_probability.lhs.variable
    
    Eq << bayes.is_nonzero.is_positive.apply(Eq[0])
    
    Eq <<= algebre.strict_greater_than.imply.strict_greater_than.integrate.apply(Eq[-1], (_y,)), \
        algebre.strict_greater_than.imply.strict_greater_than.integrate.apply(Eq[-1], (_x,))
    
    Eq <<= Eq[-2].subs(Eq.x_marginal_probability), Eq[-1].subs(Eq.y_marginal_probability)
    
    Eq <<= algebre.strict_greater_than.imply.unequal.apply(Eq[-1]) & algebre.strict_greater_than.imply.unequal.apply(Eq[-2])
    
    
if __name__ == '__main__':
    prove(__file__)
