from axiom.utility import prove, apply
from sympy import *

from axiom import sets

@apply
def apply(given):
    assert given.is_ForAll
    assert len(given.limits) == 1
    x, A = given.limits[0]
    
    assert given.function.is_Contains
    _x, B = given.function.args
    
    assert x == _x    
    return Subset(A, B)



@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.complex*n)
    B = Symbol.B(etype=dtype.complex*n)
       
    Eq << apply(ForAll[x:A](Contains(x, B)))

    Eq << Eq[0].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << Eq[-1].apply(sets.subset.imply.subset.union_comprehension.lhs, *Eq[-1].limits)    
    
if __name__ == '__main__':
    prove(__file__)

