from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan, StrictLessThan
from sympy import Symbol
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebre, sets


@apply
def apply(*given):
    is_positive_x, strict_greater_than = given
    x = axiom.is_positive(is_positive_x)
    lhs, rhs = axiom.is_StrictGreaterThan(strict_greater_than)
    return StrictGreaterThan(lhs * x, rhs * x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x > 0, a > b)
    
    Eq << Eq[1] - b
    
    Eq << algebre.is_positive.is_positive.imply.is_positive.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1] + b * x

    
if __name__ == '__main__':
    prove(__file__)
