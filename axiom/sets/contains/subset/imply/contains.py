from axiom.utility import prove, apply
from sympy import *

from axiom import sets
# given: A in B 
# => {A} subset B
@apply
def apply(*given):
    contains, subset = given
    if contains.is_Subset:
        subset, contains = given
    assert contains.is_Contains and subset.is_Subset
    x, A = contains.args
    _A, B = subset.args
    assert A == _A
    return Contains(x, B)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, A), Subset(A, B))
    
    Eq << sets.contains.imply.contains.amplify.apply(Eq[0], B)
    
    Eq << sets.subset.imply.eq.union.apply(Eq[1])
    
    Eq << Eq[-2].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

