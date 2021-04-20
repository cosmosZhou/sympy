from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import statistics, algebra
from sympy.stats.rv import pspace


# given: P(x) != 0
# imply: P(x[:t]) != 0
@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    
    eq = given.lhs.arg
    x, _x = eq.args
    assert _x == pspace(x).symbol
    n = x.shape[0]
    t = Symbol.t(domain=Interval(1, n - 1, integer=True))
    return Unequal(P(x[:t]), 0)


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(real=True, shape=(n,), random=True)
    
    Eq << apply(Unequal(P(x), 0))
    
    t = Symbol.t(domain=Interval(1, n - 1, integer=True))
    
    Eq << Eq[0].this.lhs.arg.apply(algebra.eq.imply.et.split.block_matrix, Slice[:t])
     
    Eq << statistics.is_nonzero.imply.et.apply(Eq[-1])
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    
if __name__ == '__main__':
    prove()
