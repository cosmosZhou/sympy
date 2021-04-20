from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
#     i0 + di * r < min(l * r + i0, s)
#     di < min(-1 // r + l, (s - i0 - 1) // r) + 1    
    lhs, rhs = axiom.is_Less(given)
    
    i0, di_r = axiom.is_Add(lhs)
    if not di_r.is_Mul:
        i0, di_r = di_r, i0
    di, r = axiom.is_Mul(di_r)
    
    s, lr_i0 = axiom.is_Min(rhs)
    if not lr_i0.is_Add:
        s, lr_i0 = lr_i0, s
        
    lr, _i0 = axiom.is_Add(lr_i0)
    if i0 != _i0:
        lr, _i0 = _i0, lr
        
    assert _i0 == i0
    
    l, _r = axiom.is_Mul(lr)
    if _r != r:
        l, _r = _r, l
    
    assert _r == r        
    
    return LessEqual(di, Min(-1 // r + l, (s - i0 - 1) // r))


@prove
def prove(Eq):
    di = Symbol.d_i(integer=True)
    i0 = Symbol.i0(integer=True)
    r = Symbol.r(integer=True, positive=True)
    l = Symbol.l(integer=True, positive=True)    
    s = Symbol.s(integer=True, positive=True)
    Eq << apply(i0 + di * r < Min(l * r + i0, s))   
    
    Eq << Eq[0] - i0
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.min)
    
    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.min)
    
    Eq << Eq[-1] / r
    
    Eq << algebra.le.imply.le.floor.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.floor.to.min)
    
    Eq << Eq[-1].this.rhs.args[1].arg.expand()

if __name__ == '__main__':
    prove()
