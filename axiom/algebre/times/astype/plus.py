from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self): 
    flr, d = axiom.is_Times(self)
    if d.is_Floor:
        flr, d = d, flr    
    div_x_d = axiom.is_Floor(flr)
    x, _d = axiom.is_Divide(div_x_d)
    assert d == _d
    
    assert d.is_integer and x.is_integer
    return Equality(self, x - x % d)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(x // d * d)
    
    Eq << (x % d).this.definition
    
    Eq << Eq[0] - Eq[1]

    
if __name__ == '__main__':
    prove(__file__)
