from axiom.utility import plausible
from sympy.core.relational import Unequal, Equal
from sympy import Symbol
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.function import Function
from sympy.core.numbers import Zero


@plausible
def apply(*given):
    eq, f_eq = given
    lhs, rhs = axiom.is_Unequal(eq)
    _lhs, _rhs = axiom.is_Equal(f_eq)
    old = KroneckerDelta(lhs, rhs)
    new = Zero()
    return Equal(_lhs._subs(old, new), _rhs._subs(old, new))


from axiom.utility import check


@check
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    Eq << apply(Unequal(x, y), Equal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 0, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[2].reversed
    
    
if __name__ == '__main__':
    prove(__file__)


