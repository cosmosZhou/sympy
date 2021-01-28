from axiom.utility import prove, apply
from sympy import Subset, Symbol
import axiom
from sympy.core.symbol import dtype
from axiom import sets


@apply(imply=True)
def apply(*given):
    a_less_than_x, x_less_than_b = given
    A, X = axiom.is_Subset(a_less_than_x)    
    _X, B = axiom.is_Subset(x_less_than_b)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Subset(A, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.complex)
    X = Symbol.X(etype=dtype.complex)
    B = Symbol.B(etype=dtype.complex)

    Eq << apply(Subset(A, X), Subset(X, B))
       
    Eq << sets.subset.imply.forall_contains.apply(Eq[0])
    
    Eq << Eq[-1].apply(sets.contains.subset.imply.contains, Eq[1])
    
    Eq << sets.forall_contains.imply.subset.apply(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
