from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equal
from sympy import Symbol, Boole
import axiom
from axiom import algebre
from sympy.functions.elementary.piecewise import Piecewise


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_Unequal(given)
    assert rhs.is_One
    assert lhs.is_Boole
    
    return Equal(lhs, 0)




@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(Boole(x > y), 1))
    
    Eq << Eq[0].this.lhs.astype(Piecewise)
    
    Eq << Eq[1].this.lhs.astype(Piecewise)
    
    

if __name__ == '__main__':
    prove(__file__)
