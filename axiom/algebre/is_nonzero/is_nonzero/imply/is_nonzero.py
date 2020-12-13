from axiom.utility import plausible
from sympy.core.relational import Unequal
from sympy import Symbol

import axiom


@plausible
def apply(*given):
    is_nonzero_x, is_nonzero_y = given
    x = axiom.is_nonzero(is_nonzero_x)
    y = axiom.is_nonzero(is_nonzero_y)
    return Unequal(x * y, 0)


from axiom.utility import check


@check
def prove(Eq):    
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))
    
    Eq << Eq[0] * Eq[1]
        
if __name__ == '__main__':
    prove(__file__)
