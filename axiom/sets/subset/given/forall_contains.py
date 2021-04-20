from axiom.utility import prove, apply
from sympy import *

from axiom import sets, algebra


@apply
def apply(imply):
    assert imply.is_Subset
    B, A = imply.args
    x = B.element_symbol()

    return ForAll[x:B](Contains(x, A))


@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n, given=True)
    B = Symbol.B(etype=dtype.complex * n, given=True)
    
    Eq << apply(Subset(B, A))
    
    Eq << sets.subset.given.is_emptyset.complement.apply(Eq[0])
    
    Eq << ~Eq[-1]
    
    Eq << sets.is_nonemptyset.imply.exists_contains.having.complement.apply(Eq[-1], simplify=False)
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq[1])
    

if __name__ == '__main__':
    prove()

