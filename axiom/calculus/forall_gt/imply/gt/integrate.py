from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_strict_greater_than(given)
    lhs, rhs = eq.args
    
    return StrictGreaterThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](StrictGreaterThan(f(x), g(x))))
    

if __name__ == '__main__':
    prove(__file__)

