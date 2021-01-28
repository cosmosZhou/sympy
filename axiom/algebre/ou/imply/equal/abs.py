from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets, algebre


@apply(imply=True)
def apply(given):
    equal_positive, equal_negative = axiom.is_Or(given)
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
    
    Eq << Eq[0].this.args[0].apply(algebre.equal.imply.equal.abs)
    
    Eq << Eq[-1].this.args[0].apply(algebre.equal.imply.equal.abs)
    
    

if __name__ == '__main__':
    prove(__file__)

