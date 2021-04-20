from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given): 
    equal, cond = given
    b, x = axiom.is_Equal(equal)
    _x, a = axiom.is_BinaryCondition(cond)
    
    if x != _x:
        b, x = x, b    
    
    assert x == _x
 
    return cond.func(b, a)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(Equal(x, y), x >= t)
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    
if __name__ == '__main__':
    prove()
