from sympy import *
from axiom.utility import prove, apply
import axiom
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, complement = axiom.is_Contains(given)
    U, y = axiom.is_Complement(complement)
    assert U.is_UniversalSet
    y = axiom.is_FiniteSet(y)
    return Unequality(x, y)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    y = Symbol.y(complex=True, shape=(n,), given=True)
    Eq << apply(Contains(x, y.universalSet // {y}))
    
    Eq << Eq[0].simplify()
        

if __name__ == '__main__':
    prove(__file__)

