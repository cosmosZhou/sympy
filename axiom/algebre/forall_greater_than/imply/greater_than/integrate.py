from axiom.utility import prove, apply
from sympy.core.relational import Equality, GreaterThan
from sympy import Symbol, ForAll, Slice, Integrate
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_greater_than(given)
    lhs, rhs = eq.args
    
    return GreaterThan(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](GreaterThan(f(x), g(x))))
    

if __name__ == '__main__':
    prove(__file__)

