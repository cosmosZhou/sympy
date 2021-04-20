from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete
import axiom

from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given):
    xj, *limits = axiom.forall_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 0
    x, _j = axiom.is_Indexed(xj)
    assert _j == j
    return Unequal(alpha(x[:n]), 0)


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    Eq << apply(ForAll[i:0:n](x[i] > 0))
    
    x_ = Symbol.x(real=True, positive=True, shape=(oo,))
    Eq << discrete.imply.is_nonzero.alpha.apply(x_[:n])
    
    Eq << Eq[-1].subs(x_[:n], x[:n])
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[-1])
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove()

from . import offset