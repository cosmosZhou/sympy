from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete, sets
import axiom
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given): 
    xj, *limits = axiom.forall_is_positive(given)
    j, a, n = axiom.limit_is_Interval(limits)
    assert a == 1
    x, _j = axiom.is_Indexed(xj)
    assert _j == j
    
    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    Eq << apply(ForAll[i:1:n + 2](x[i] > 0))
    
    Eq << discrete.imply.sufficient.alpha.recurrence.apply(alpha(x[:n + 2]))
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    prove()

