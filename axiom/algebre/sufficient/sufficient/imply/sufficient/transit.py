from axiom.utility import prove, apply
from sympy import Symbol, Or
import axiom
from sympy.logic.boolalg import Sufficient
from axiom import algebre


@apply(imply=True)
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
    
    Eq << Eq[0].astype(Or)
        
    Eq << Eq[1].astype(Or)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].astype(Or)
        
    Eq << Eq[2].astype(Or)
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq[-1].astype(Or)
    
    
if __name__ == '__main__':
    prove(__file__)
