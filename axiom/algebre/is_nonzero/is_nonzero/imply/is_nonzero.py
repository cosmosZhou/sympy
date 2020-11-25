from axiom.utility import plausible
from sympy.core.relational import Equal, Unequal
from sympy import Symbol

from sympy.core.numbers import oo

from sympy.concrete.expr_with_limits import ForAll, LAMBDA
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity



@plausible
def apply(*given):
    is_nonzero_x, is_nonzero_y = given
    x = axiom.is_nonzero(is_nonzero_x)
    y = axiom.is_nonzero(is_nonzero_y)
    return Unequal(x * y, 0, given=given)


from axiom.utility import check


@check
def prove(Eq):    
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))
    
    Eq << Eq[0] * Eq[1]
        
if __name__ == '__main__':
    prove(__file__)
