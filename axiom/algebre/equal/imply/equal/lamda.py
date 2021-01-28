from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.core.function import Function
import axiom

from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre


@apply(imply=True)
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(LAMBDA(lhs, *limits).simplify(), LAMBDA(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    
    Eq << apply(Equality(f(i), g(i)), (i,))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], LAMBDA[i], simplify=False)


if __name__ == '__main__':
    prove(__file__)

