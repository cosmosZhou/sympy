from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Integrate
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply(imply=True)
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(Integrate(lhs, *limits).simplify(), Integrate(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(x), g(x)), (x, -oo, oo))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], Integrate[x:-oo:oo], simplify=False)    


if __name__ == '__main__':
    prove(__file__)

