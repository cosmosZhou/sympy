
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.relational import Equal

from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from sympy import And
from axiom.algebre.condition.condition.imply.condition import process_given_conditions
from axiom import algebre

@apply(imply=True)
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)    
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))

    Eq << algebre.condition.condition.imply.condition.apply(Eq[0], Eq[1])
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove(__file__)

