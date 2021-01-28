
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function

from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_Exists
    return Exists(given.limits_condition, *given.limits)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)    

    Eq << apply(Exists[e:S](f(e) > 0))
    
    Eq << Eq[1].simplify()
    
    Eq << sets.exists.imply.is_nonemptyset.apply(Eq[0])


if __name__ == '__main__':
    prove(__file__)

