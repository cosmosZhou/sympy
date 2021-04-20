from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, factor): 
    base, e = axiom.is_Pow(self)
    assert e == -1
    assert factor.is_nonzero
    
    return Equal(self, factor / (base * factor).expand())


@prove
def prove(Eq):
    b = Symbol.b(real=True, positive=True)

    d = Symbol.d(real=True, positive=True)

    Eq << apply(1 / (b + 1 / d), d)   

    Eq << (d * (b + 1 / d)).this.expand()
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
if __name__ == '__main__':
    prove()
