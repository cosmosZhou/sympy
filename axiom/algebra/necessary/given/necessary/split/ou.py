from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fx, ou = axiom.is_Necessary(given)
    eqs = axiom.is_Or(ou)    
    return tuple(Necessary(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    b = Symbol.b(integer=True)
    a = Symbol.a(integer=True)
    
    Eq << apply(Necessary(f(x) > g(x), (a > b) | (f(a) > f(b))))
    
    Eq << algebra.necessary.necessary.imply.necessary.ou.apply(Eq[1], Eq[2])
        
if __name__ == '__main__':
    prove()
