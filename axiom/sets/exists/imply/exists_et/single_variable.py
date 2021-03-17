from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given):
    function, *limits = axiom.is_Exists(given)
    lhs, rhs = axiom.limit_is_set(limits)
    return Exists[lhs]((function & Contains(lhs, rhs)).simplify())


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:S](f(e) > 0))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

