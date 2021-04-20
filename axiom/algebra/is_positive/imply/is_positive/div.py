from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, num=1, evaluate=False):
    x = axiom.is_positive(given)
    assert num > 0
    return Greater(num / x, 0, evaluate=evaluate)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    d = Symbol.d(real=True, positive=True)
        
    Eq << apply(x > 0, num=d)
    
    Eq << Eq[-1] / d
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Eq[-1].apply(algebra.is_nonpositive.is_positive.imply.is_nonpositive)

    
if __name__ == '__main__':
    prove()

