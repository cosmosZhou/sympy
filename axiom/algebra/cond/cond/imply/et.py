from sympy import *
from axiom.utility import prove, apply
from axiom.algebra.cond.cond.imply.cond import process_given_conditions
from axiom import algebra


@apply
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)    
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)    
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(NotContains(x, S), Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))

    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[1])
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()

