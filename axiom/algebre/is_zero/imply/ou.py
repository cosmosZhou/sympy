from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol
import axiom
from sympy.logic.boolalg import Or
from axiom import algebre


@apply(imply=True)
def apply(given):
    multiply = axiom.is_zero(given)
    args = axiom.is_Times(multiply)
    
    return Or(*(Equal(arg, 0).simplify() for arg in args))




@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(a * b, 0))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].apply(algebre.is_nonzero.is_nonzero.imply.is_nonzero)
    
    Eq <<= Eq[-1] & Eq[0]
    
    

if __name__ == '__main__':
    prove(__file__)
