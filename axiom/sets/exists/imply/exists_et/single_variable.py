
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
import axiom


@apply(imply=True)
def apply(given):
    function, *limits = axiom.is_Exists(given)
    contains = axiom.limit_is_set(limits)
    return Exists[contains.lhs]((function & contains).simplify())




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:S](f(e) > 0))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

