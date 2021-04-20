from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import Supset
from sympy.core.numbers import oo
from axiom import algebra, sets
import axiom


@apply
def apply(*given):
    subset_ab, subset_xy = given
    a, b = axiom.is_Supset(subset_ab)
    x, y = axiom.is_Supset(subset_xy)
    
    return Supset(a | x, b | y)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    X = Symbol.X(etype=dtype.integer)
    Y = Symbol.Y(etype=dtype.integer)
    
    Eq << apply(Supset(A, B), Supset(X, Y))
    
    Eq <<= Eq[0].reversed, Eq[1].reversed

    Eq << sets.subset.subset.imply.subset.union.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].reversed
    
if __name__ == '__main__':
    prove()

