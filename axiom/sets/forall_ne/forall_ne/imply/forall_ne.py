from sympy import *
from axiom.utility import prove, apply
from axiom import algebre

# given: 
#     ForAll[j:Interval(0, n - 1, integer=True) - {i}, i:n](Unequality(x[i], x[j]))
#     ForAll[i:n](Unequality(x[n], x[i])))

# ForAll[j:Interval(0, n, integer=True) - {i}, i:n+1](Unequality(x[i], x[j]))


@apply
def apply(*given):
    forall_historic, forall_n = given
    assert forall_historic.is_ForAll and forall_n.is_ForAll
    
    if len(forall_historic.limits) == 1:
        forall_historic, forall_n = forall_n, forall_historic
    (j, _zero, i_1), (_i, zero, n_1) = forall_historic.limits    
    assert zero.is_zero and _zero.is_zero 
    
    assert len(forall_n.limits) == 1
    i, zero, _n_1 = forall_n.limits[0]
    assert i == i_1
    assert zero.is_zero
    assert _n_1 == n_1
    n = n_1
    
    assert forall_historic.function.is_Unequality and forall_n.function.is_Unequality
    lhs, rhs = forall_historic.function.args
    if lhs._has(j):
        lhs, rhs = rhs, lhs     
    x = LAMBDA[i:n + 1](lhs)
    assert x[j] == rhs
    
    lhs, rhs = forall_n.function.args
    if lhs._has(i):
        lhs, rhs = rhs, lhs
        
    assert x[n] == lhs
    assert x[i] == rhs
    
    return ForAll[j:i, i:n + 1](Unequality(x[i], x[j]))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
 
    Eq << apply(ForAll[j:i, i:n](Unequality(x[i], x[j])),
                ForAll[i:n](Unequality(x[n], x[i])))

    Eq << Eq[-1].bisect({n}, wrt=i)
    
    Eq << algebre.et.given.cond.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

