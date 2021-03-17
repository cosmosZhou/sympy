from sympy import *
from axiom.utility import prove, apply
import axiom

from axiom import algebre, sets, calculus


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_GreaterThan(given)
    
    return GreaterThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(GreaterThan(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebre.cond.imply.forall.restrict, (x, a, b))    
    
    Eq << calculus.forall_ge.imply.ge.integrate.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

