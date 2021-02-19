
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
import axiom
from sympy.logic.boolalg import And


@apply
def apply(given):
    function, *limits = axiom.is_Exists(given)
    variables = axiom.limits_are_Contains(limits)    
    return Exists[variables](And(function, given.limits_condition).simplify())




@prove
def prove(Eq):    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    f = Function.f(nargs=(2,), shape=(), integer=True)

    Eq << apply(Exists[x:A, y:B](f(x, y) > 0))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

