from axiom.utility import prove, apply
from sympy.core.relational import LessThan
from sympy import Symbol
import axiom
from axiom import algebre


@apply
def apply(*given):
    greater_than, less_than = given
    x, a = axiom.is_GreaterThan(greater_than)
    y, b = axiom.is_LessThan(less_than)
    
    return LessThan((x - a) * (y - b), 0)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x >= a, y <= b)   
    
    Eq << Eq[1].reversed
    
    Eq << algebre.greater_than.greater_than.imply.is_nonnegative.apply(Eq[0], Eq[-1])
    Eq << -Eq[-1]
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[2].this.lhs.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
