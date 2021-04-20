from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.continued_fraction.HK.definition import K


@apply
def apply(given): 
    ge, *limits = axiom.forall_ge(given)
        
    xj, one = ge.args
    assert one == 1
    
    j, a, n1 = axiom.limit_is_Interval(limits)
    assert a == 1
    n = n1 - 1
    x, _j = axiom.is_Indexed(xj)
    assert _j == j
    
    return GreaterEqual(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(ForAll[i:1:n + 1](x[i] >= 1))
    
    Eq << discrete.imply.sufficient.ge.K.apply(x[:n + 1])
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove()

