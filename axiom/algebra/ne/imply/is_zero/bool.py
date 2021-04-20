from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    lhs, rhs = axiom.is_Unequal(given)
    assert rhs.is_One
    assert lhs.is_Bool
    
    return Equal(lhs, 0)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(Bool(x > y), 1))
    
    Eq << Eq[0].this.lhs.definition
    
    Eq << Eq[1].this.lhs.definition
    

if __name__ == '__main__':
    prove()
