from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(fraction):
    x = axiom.is_FractionalPart(fraction)
    x = axiom.is_Negate(x)
    x, two = axiom.is_Divide(x)
    assert two == 2
     
    return Equality(fraction, frac(x / 2))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    Eq << apply(frac(-n / 2))
    
    Eq << Eq[0].bisect(Equal(n % 2, 0))
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq <<= algebre.imply.forall.limits_assert.apply(Eq[-2].limits).this.function.apply(algebre.is_even.imply.exists), algebre.imply.forall.limits_assert.apply(Eq[-1].limits).this.function.apply(algebre.is_odd.imply.exists)
    
    Eq << Eq[2].subs(Eq[-2])     
    
    Eq << Eq[3].subs(Eq[-1])
    

    
if __name__ == '__main__':
    prove(__file__)
