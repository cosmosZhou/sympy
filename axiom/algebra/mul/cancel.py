from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(simplify=False)
def apply(self, factor): 
    num, den = axiom.is_Divide(self)
    factor = sympify(factor)
    assert factor.is_nonzero
    
    return Equal(self, (num * factor).expand() / (den * factor).expand(), evaluate=False)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True, zero=False)
    d = Symbol.d(real=True, zero=False)

    Eq << apply((a + 1 / c) / (b + 1 / d), c * d)   
    
    Eq << (c * d * (b + 1 / d)).this.expand()
    
    Eq << (c * d * (a + 1 / c)).this.expand()
    
    Eq << Eq[0].subs(Eq[-2].reversed, Eq[-1].reversed)
    
if __name__ == '__main__':
    prove()
