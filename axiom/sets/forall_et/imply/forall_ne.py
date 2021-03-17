from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(given):
    assert given.is_ForAll
    
    assert len(given.limits) == 1
    i, zero, n_1 = given.limits[0]
    assert zero.is_zero
    
    et = given.function
    assert et.is_And
    
    forall_historic, forall_n = et.args
    if forall_n.is_ForAll:
        forall_n, forall_historic = et.args
        
    assert forall_historic.is_ForAll
    
    assert len(forall_historic.limits) == 1
    j, zero, i_1 = forall_historic.limits[0]
        
    assert zero.is_zero 
    
    assert i == i_1
    
    n = n_1
    
    assert forall_historic.function.is_Unequality and forall_n.is_Unequality
    lhs, rhs = forall_historic.function.args
    if lhs._has(j):
        lhs, rhs = rhs, lhs     
    x = LAMBDA[i:n + 1](lhs)
    assert x[j] == rhs
    
    lhs, rhs = forall_n.args
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
 
    Eq << apply(ForAll[i:n](Unequality(x[n], x[i]) & ForAll[j:i](Unequality(x[i], x[j]))))

    Eq << algebre.forall_et.imply.forall.apply(Eq[0])

    Eq << sets.forall_ne.forall_ne.imply.forall_ne.apply(Eq[-1], Eq[-2])

    
if __name__ == '__main__':
    prove(__file__)

