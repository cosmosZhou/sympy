from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
import axiom

from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.continued_fraction.HK.definition import H, K


@apply
def apply(given):
    xj, *limits = axiom.forall_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 0
    x, _j = axiom.is_Indexed(xj)
    offset = _j - j
    if offset != 0: 
        assert not offset._has(j)
        x = x[offset:]
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    Eq << apply(ForAll[i:0:n](x[i] > 0))
    
    x_ = Symbol.x(real=True, positive=True, shape=(oo,))
    Eq << discrete.continued_fraction.alpha.HK.provided.is_positive.apply(x_[:n])
    
    Eq << Eq[-1].subs(x_[:n], x[:n])
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[-1])
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove()

