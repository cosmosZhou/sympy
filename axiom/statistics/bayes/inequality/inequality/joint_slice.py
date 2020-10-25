
from sympy.core.relational import Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol, Slice
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes

from sympy.stats.rv import pspace
from sympy.core.numbers import oo


# given: P(x, y) != 0
# imply: P(x[:t], y[:t]) != 0
@plausible
def apply(given, indices):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    
    eqs = given.lhs.arg
    assert eqs.is_And
    
    args = []
    for eq, t in zip(eqs.args, indices):        
        x, _x = eq.args
        assert _x == pspace(x).symbol
        args.append(x[t])
        
    return Unequal(P(*args), 0, given=given)


@check
def prove(Eq):
    n = Symbol.n(integer=True, domain=[2, oo])
    x = Symbol.x(real=True, shape=(n,), random=True)
    y = Symbol.y(real=True, shape=(n,), random=True)
    t = Symbol.t(integer=True, domain=[1, n - 1])
    
    Eq << apply(Unequal(P(x, y), 0), Slice[:t, :t])
    
    Eq << Eq[0].this.lhs.arg.args[-1].bisect(Slice[:t])
    
    Eq << Eq[-1].this.lhs.arg.args[0].bisect(Slice[:t])
 
    Eq << bayes.inequality.et.apply(Eq[-1], wrt={x[:t], y[:t]}).split()
    
    
if __name__ == '__main__':
    prove(__file__)
