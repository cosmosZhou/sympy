from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equal
from sympy import Symbol
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.function import Function
from sympy.core.numbers import Zero
from sympy.logic.boolalg import And, BooleanFalse, BooleanTrue
from axiom.algebre.unequal.condition.imply.condition import process_given_conditions


@apply(imply=True)
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)    
    return And(eq, f_eq.simplify())




@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    Eq << apply(Unequal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 0, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    
    
if __name__ == '__main__':
    prove(__file__)

