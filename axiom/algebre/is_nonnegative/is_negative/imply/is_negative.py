from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan, StrictLessThan,\
    LessThan
from sympy import Symbol
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre, sets


@apply
def apply(*given):
    is_positive_x, is_negative_y = given
    x = axiom.is_nonnegative(is_positive_x)
    y = axiom.is_negative(is_negative_y)
    return LessThan(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x >= 0, y < 0)
    
#     Eq << Eq[1] * Eq[0]
    
    Eq << Eq[0] * Eq[1]    

    
if __name__ == '__main__':
    prove(__file__)
