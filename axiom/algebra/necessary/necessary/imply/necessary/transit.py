from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    is_imply_P, is_imply_Q = given
    p, q = axiom.is_Sufficient(is_imply_P)    
    _q, r = axiom.is_Sufficient(is_imply_Q)
    if q != _q:
        p, q, _q, r = _q, r, p, q
         
    assert q == _q
    return Sufficient(p, r)


@prove
def prove(Eq):
    p = Symbol.p(real=True, given=True)
    q = Symbol.q(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Sufficient(p > q, x > y), Sufficient(x > y, a > b))
#     Eq << apply(Sufficient(x > y, a > b), Sufficient(p > q, x > y))
    
    Eq << Eq[0].apply(algebra.sufficient.imply.ou)
        
    Eq << Eq[1].apply(algebra.sufficient.imply.ou)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
        
    Eq << Eq[2].apply(algebra.sufficient.given.ou)
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
    
if __name__ == '__main__':
    prove()
