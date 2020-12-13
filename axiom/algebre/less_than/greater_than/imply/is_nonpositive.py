from axiom.utility import plausible
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
import axiom
from axiom import algebre


@plausible
def apply(*given):
    less_than_0, greater_than = given
    x, a = axiom.is_LessThan(less_than_0)
    y, b = axiom.is_GreaterThan(greater_than)
    
    return LessThan((x - a) * (y - b), 0)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x <= a, y >= b)
    
    Eq << Eq[1].reversed   
    
    Eq << algebre.less_than.less_than.imply.is_nonnegative.apply(Eq[0], Eq[-1])
    
    Eq << -Eq[-1]
    
    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()
        
if __name__ == '__main__':
    prove(__file__)

