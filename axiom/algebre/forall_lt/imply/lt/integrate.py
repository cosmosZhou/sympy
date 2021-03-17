from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets, calculus


@apply
def apply(given):
    eq, *limits = axiom.forall_strict_less_than(given)
    lhs, rhs = eq.args
    
    return StrictLessThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](StrictLessThan(f(x), g(x))))
    
    Eq << Eq[0].reversed
    
    Eq << calculus.forall_gt.imply.gt.integrate.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

