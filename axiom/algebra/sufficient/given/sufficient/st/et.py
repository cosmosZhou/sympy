from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    cond, et = axiom.is_Sufficient(given)
    eqs = axiom.is_And(et)        
    return tuple(Sufficient(cond, eq) for eq in eqs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    x = Symbol.x(integer=True, nonnegative=True)
    y = Symbol.y(integer=True, nonnegative=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)
    
    Eq << apply(Sufficient(x > y, (f(x) > g(y)) & (f(x) > h(y))))
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.et.apply(Eq[1], Eq[2])
    
    
        
if __name__ == '__main__':
    prove()
