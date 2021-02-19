from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan
from sympy import Symbol, ForAll, Integrate
from sympy.core.function import Function
import axiom
from axiom import algebre


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_StrictGreaterThan(given)
    
    return StrictGreaterThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(StrictGreaterThan(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (x, a, b))
    
    Eq << algebre.forall_strict_greater_than.imply.strict_greater_than.integrate.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

