from sympy import *
from axiom.utility import prove, apply
from axiom.algebre.eq.cond.imply.cond.kronecker_delta import process_given_conditions


@apply
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)    
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    Eq << apply(Equal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    
    
if __name__ == '__main__':
    prove(__file__)

