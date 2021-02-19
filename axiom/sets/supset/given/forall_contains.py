from axiom.utility import prove, apply
from sympy import *

from axiom import sets, algebre


@apply
def apply(imply):
    assert imply.is_Supset
    A, B = imply.args
    x = B.element_symbol()
   
    return ForAll[x:B](Contains(x, A))


@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n, given=True)
    B = Symbol.B(etype=dtype.complex * n, given=True)
    
    Eq << apply(Supset(B, A))
    
    Eq << Eq[0].reversed

    Eq << sets.subset.given.forall_contains.apply(Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

