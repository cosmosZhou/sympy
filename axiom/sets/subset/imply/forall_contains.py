from axiom.utility import prove, apply
from sympy import *

from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_Subset
    B, A = given.args
    x = B.element_symbol()
   
    return ForAll[x:B](Contains(x, A))


@prove
def prove(Eq):
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    
    Eq << apply(Subset(B, A))
    
    x = Eq[1].variable
    Eq << ForAll[x:B](Contains(x, B), plausible=True)
    
    Eq << Eq[-1].simplify()

    Eq << Eq[-1].apply(sets.contains.subset.imply.contains, Eq[0], join=False)


if __name__ == '__main__':
    prove(__file__)

