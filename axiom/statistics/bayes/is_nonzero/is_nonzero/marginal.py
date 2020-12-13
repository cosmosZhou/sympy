
from sympy.core.relational import Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes


# given: P(x | y) != 0
# imply: P(x) != 0
@plausible
def apply(given):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    eq = given.lhs.arg
    assert eq.is_Conditioned     
    return Unequal(P(eq.lhs), 0)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x | y), 0))
    
    Eq << bayes.is_nonzero.is_nonzero.joint.apply(Eq[0])

    Eq << bayes.is_nonzero.et.apply(Eq[-1]).split()
    
if __name__ == '__main__':
    prove(__file__)
