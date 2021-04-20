from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import K


@apply
def apply(given): 
    xj, *limits = axiom.forall_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 1
    x, _j = axiom.is_Indexed(xj)
    assert _j == j
    
    return Greater(K(x[:n]), 0)


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(ForAll[i:1:n](x[i] > 0))
    
    Eq << discrete.imply.sufficient.is_positive.K.apply(x[:n])
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
    
if __name__ == '__main__':
    prove()

