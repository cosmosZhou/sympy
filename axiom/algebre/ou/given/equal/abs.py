from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets, algebre


@apply(given=True)
def apply(imply):
    equal_positive, equal_negative = axiom.is_Or(imply)
    y, x = axiom.is_Equal(equal_positive)
    _y, _x = axiom.is_Equal(equal_negative)
    if y != _y:
        _y, _x = _x, _y
            
    assert y == _y
    assert x == -_x
    
    return Equality(abs(y), abs(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(Equality(y, x) | Equality(y, -x))
    
    Eq << Eq[-1] ** 2
    
    Eq << Eq[-1] - Eq[-1].rhs
    
    Eq << Eq[-1].this.lhs.factor()
    
    Eq << algebre.is_zero.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0] - x
    
    

if __name__ == '__main__':
    prove(__file__)

