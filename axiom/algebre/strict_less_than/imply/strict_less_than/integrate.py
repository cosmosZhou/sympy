from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictLessThan
from sympy import Symbol, ForAll, Slice, Integrate
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_StrictLessThan(given)
    
    return StrictLessThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(StrictLessThan(f(x), g(x)), (x, a, b))
    
    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (x, a, b))
    
    Eq << algebre.forall_strict_less_than.imply.strict_less_than.integrate.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

