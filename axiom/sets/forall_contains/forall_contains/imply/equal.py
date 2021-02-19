from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import ForAll
from axiom import sets
from sympy.sets.contains import Contains


@apply
def apply(*given):
    forall_A, forall_B = given
    assert forall_A.is_ForAll and forall_B.is_ForAll
    assert len(forall_A.limits) == len(forall_B.limits) == 1
    x, A = forall_A.limits[0]
    _x, B = forall_B.limits[0]
    assert x == _x
    
    assert forall_A.function.is_Contains
    _x, _B = forall_A.function.args
    
    assert x == _x and B == _B
    assert forall_B.function.is_Contains
    _x, _A = forall_B.function.args
    assert x == _x and A == _A
    
    return Equality(A, B)



@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer*n)
    B = Symbol.B(etype=dtype.integer*n)
    
    Eq << apply(ForAll[x:A](Contains(x, B)), ForAll[x:B](Contains(x, A)))
    
    Eq << sets.forall_contains.imply.subset.apply(Eq[0])
    
    Eq << sets.forall_contains.imply.subset.apply(Eq[1])
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove(__file__)

