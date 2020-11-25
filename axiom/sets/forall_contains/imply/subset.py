from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.concrete.expr_with_limits import ForAll
from axiom import sets
from sympy.sets.contains import Contains, Subset


@plausible
def apply(given):
    assert given.is_ForAll
    assert len(given.limits) == 1
    x, A = given.limits[0]
    
    assert given.function.is_Contains
    _x, B = given.function.args
    
    assert x == _x    
    return Subset(A, B, given=given)

from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.complex*n)
    B = Symbol.B(etype=dtype.complex*n)
       
    Eq << apply(ForAll[x:A](Contains(x, B)))

    Eq << Eq[0].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << Eq[-1].apply(sets.subset.imply.subset, *Eq[-1].limits)    
    
if __name__ == '__main__':
    prove(__file__)

