from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
        
    assert lhs.is_FiniteSet
    args = [Contains(lhs, rhs).simplify() for lhs in lhs.args]               
        
    return And(*args)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    S = Symbol.S(etype=dtype.real)
    Eq << apply(Equality({a, b}, S))    
    
    Eq << algebre.et.given.cond.apply(Eq[1])
    
    Eq << Contains(a, {a, b}, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Contains(b, {a, b}, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    prove(__file__)

