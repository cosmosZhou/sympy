from axiom.utility import prove, apply
from sympy import *
from axiom import algebre, sets
import axiom


@apply(imply=True)
def apply(*given):
    subset_ab, subset_xy = given
    a, b = axiom.is_Subset(subset_ab)
    x, y = axiom.is_Subset(subset_xy)
    
    return Subset(a | x, b | y)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    X = Symbol.X(etype=dtype.integer)
    Y = Symbol.Y(etype=dtype.integer)
    
    Eq << apply(Subset(A, B), Subset(X, Y))
    
    Eq << sets.subset.imply.subset.amplify.apply(Eq[0], Y)
    
    Eq << sets.subset.imply.subset.amplify.apply(Eq[1], B)
    
    Eq <<= Eq[-1] & Eq[-2]
    
if __name__ == '__main__':
    prove(__file__)

