from util import *


@apply
def apply(is_nonnegative, is_nonpositive):
    x = is_nonnegative.of(Expr >= 0)
    _x = is_nonpositive.of(Expr <= 0)
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
