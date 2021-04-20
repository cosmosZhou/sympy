from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(fraction):
    x = axiom.is_FractionalPart(fraction)
    x = axiom.is_Negate(x)
    x, two = axiom.is_Divide(x)
    assert two == 2
     
    return Equal(fraction, frac(x / 2))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    Eq << apply(frac(-n / 2))
    
    Eq << Eq[0].apply(algebra.cond.given.et.forall, cond=Equal(n % 2, 0))
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq <<= algebra.imply.forall.limits_assert.apply(Eq[-2].limits).this.function.apply(algebra.is_even.imply.exists), algebra.imply.forall.limits_assert.apply(Eq[-1].limits).this.function.apply(algebra.is_odd.imply.exists)
    
    Eq <<= Eq[2] & Eq[-2], Eq[3] & Eq[-1]
    
    Eq <<= Eq[-2].this.function.apply(algebra.et.given.exists_et, simplify=None), Eq[-1].this.function.apply(algebra.et.given.exists_et, simplify=None)
    
    Eq << Eq[-2].this.function.function.apply(algebra.et.given.et.subs.eq, index=1)
    
    Eq << Eq[-1].this.function.function.apply(algebra.et.given.et.subs.eq, index=1)
        
if __name__ == '__main__':
    prove()
