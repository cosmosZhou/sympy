from axiom.utility import prove, apply
from sympy.core.relational import Unequal
from sympy import Symbol
import axiom
from sympy.logic.boolalg import And
from sympy.matrices.expressions.matexpr import ZeroMatrix


@apply(imply=True)
def apply(given):
    multiply = axiom.is_nonzero(given)
    args = axiom.is_Times(multiply)
    return And(*(Unequal(arg, ZeroMatrix(*arg.shape)).simplify() for arg in args))




@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(a * b, 0))
    
    Eq << Eq[-1].split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])
    
    

if __name__ == '__main__':
    prove(__file__)
