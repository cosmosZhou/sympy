from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    ou, fx = axiom.is_Sufficient(given)
    eqs = axiom.is_Or(ou)    
    return tuple(Sufficient(eq, fx) for eq in eqs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    b = Symbol.b(integer=True)
    a = Symbol.a(integer=True)
    
    Eq << apply(Sufficient((a > b) | (f(a) > f(b)), f(x) > g(x)))
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq[1], Eq[2])
        
if __name__ == '__main__':
    prove()
