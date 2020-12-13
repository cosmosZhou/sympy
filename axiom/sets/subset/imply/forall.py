from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Subset, Contains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom import sets
from sympy.core.function import Function
from sympy import ForAll


@plausible
def apply(given):
    assert given.is_Subset
    B, A = given.args
    x = B.element_symbol()
   
    return ForAll[x:B](Contains(x, A))


from axiom.utility import check


@check
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

