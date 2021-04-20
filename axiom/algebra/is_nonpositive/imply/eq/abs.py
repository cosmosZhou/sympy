from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol
import axiom
from axiom import algebra


@apply
def apply(given):
    x = axiom.is_nonpositive(given)
    return Equal(abs(x), -x)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x <= 0)
    
    Eq << -Eq[0]
    
    Eq << algebra.is_nonnegative.imply.eq.abs.apply(Eq[-1])
    
    
if __name__ == '__main__':
    prove()
