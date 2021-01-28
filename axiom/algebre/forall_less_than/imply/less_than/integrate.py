from axiom.utility import prove, apply
from sympy.core.relational import Equality, LessThan
from sympy import Symbol, ForAll, Slice, Integrate
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_less_than(given)
    lhs, rhs = eq.args
    
    return LessThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](LessThan(f(x), g(x))))
    
    Eq << Eq[0].reversed
    
    Eq << algebre.forall_greater_than.imply.greater_than.integrate.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

