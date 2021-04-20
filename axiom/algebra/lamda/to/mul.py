from sympy.core.relational import Equal
from axiom.utility import prove, apply

from sympy import Symbol

import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebra
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

@apply
def apply(lamda):
    function, *limits = axiom.is_LAMBDA(lamda)
    
    (i, zero, n_1), (j, _zero, _n_1) = axiom.limits_are_Interval(limits, integer=True)
    assert zero.is_Zero and _zero.is_Zero
    assert n_1 == _n_1
    
    n = n_1
    
    lhs, rhs = axiom.is_Mul(function)
    if lhs.is_KroneckerDelta:
        lhs, rhs = rhs, lhs
        
    _i, _j = axiom.is_KroneckerDelta(rhs)
    assert i == _i and j == _j or i == _j and j == _i
    
    
    if lhs._has(j):
        assert not lhs._has(i)
        return Equal(lamda, Identity(n) * LAMBDA[j:n](lhs).simplify())
    elif lhs._has(i):
        assert not lhs._has(j)
        return Equal(lamda, Identity(n) * LAMBDA[i:n](lhs).simplify())        


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(oo,))
     
    Eq << apply(LAMBDA[j:n, i:n](a[j] * KroneckerDelta(i, j)))
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    prove()

