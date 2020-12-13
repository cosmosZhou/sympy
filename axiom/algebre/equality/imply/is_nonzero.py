from axiom.utility import plausible
from sympy.core.relational import Equality, GreaterThan, Unequal
from sympy import Symbol
import axiom


@plausible
def apply(given):    
    lhs, rhs = axiom.is_Equal(given)
    if lhs.is_nonzero:
        x = rhs
    if rhs.is_nonzero:
        x = lhs
        
    return Unequal(x, 0)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, zero=False)
    Eq << apply(Equality(a, b))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove(__file__)
