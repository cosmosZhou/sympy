from axiom.utility import plausible
from sympy.core.relational import Unequal, Equal
from sympy import Symbol
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.function import Function
from sympy.core.numbers import Zero
from sympy.logic.boolalg import And, BooleanFalse, BooleanTrue


@plausible
def apply(*given, bool=None, invert=None, reverse=None, swap=None):    
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given    
    lhs, rhs = axiom.is_Unequal(eq)
    _lhs, _rhs = axiom.is_Unequal(f_eq)
    if bool:
        if invert:
            old = eq.invert()
            new = BooleanFalse()
        else:
            old = eq
            new = BooleanTrue()
            
        if reverse:
            old = old.reversed
    else:
        old = KroneckerDelta(lhs, rhs)
        new = Zero()    
    return And(eq, Unequal(_lhs._subs(old, new), _rhs._subs(old, new)).simplify())


from axiom.utility import check


@check
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

