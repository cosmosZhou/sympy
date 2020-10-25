
from sympy.core.relational import Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol, Slice
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes

from sympy.stats.rv import pspace
from sympy.core.numbers import oo


# given: P(x) != 0
# imply: P(x[:t]) != 0
@plausible
def apply(given):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    
    eq = given.lhs.arg
    x, _x = eq.args
    assert _x == pspace(x).symbol
    n = x.shape[0]
    t = Symbol.t(integer=True, domain=[1, n - 1])
    return Unequal(P(x[:t]), 0, given=given)


@check
def prove(Eq):
    n = Symbol.n(integer=True, domain=[2, oo])
    x = Symbol.x(real=True, shape=(n,), random=True)
    
    Eq << apply(Unequal(P(x), 0))
    
    t = Symbol.t(integer=True, domain=[1, n - 1])
    
    Eq << Eq[0].this.lhs.arg.bisect(Slice[:t])
     
    Eq << bayes.inequality.et.apply(Eq[-1]).split()
    
    
if __name__ == '__main__':
    prove(__file__)
