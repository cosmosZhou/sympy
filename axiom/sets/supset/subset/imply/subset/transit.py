from axiom.utility import prove, apply
from sympy import Subset, Symbol, Supset
import axiom
from sympy.core.symbol import dtype
from axiom import sets


@apply(imply=True)
def apply(*given):
    a_less_than_x, x_less_than_b = given
    X, A = axiom.is_Supset(a_less_than_x)    
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

    Eq << apply(Supset(X, A), Subset(X, B))
       
    Eq << Eq[0].reversed
    
    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[1])
    

if __name__ == '__main__':
    prove(__file__)
