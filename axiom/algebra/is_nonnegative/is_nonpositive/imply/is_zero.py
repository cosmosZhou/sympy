
from util import *
import axiom


@apply
def apply(*given):
    is_nonnegative, is_nonpositive = given
    x = axiom.is_nonnegative(is_nonnegative)
    _x = axiom.is_nonpositive(is_nonpositive)
    assert x == _x
    return Equal(x, 0)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0, x <= 0)
    
    Eq <<= Eq[0] & Eq[1]   
    
    Eq << Eq[-1].simplify()
        
    
if __name__ == '__main__':
    run()
