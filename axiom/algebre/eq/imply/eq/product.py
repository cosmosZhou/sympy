from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(), complex=True)
    g = Function.g(nargs=(), shape=(), complex=True)
    
    Eq << apply(Equality(f(i), g(i)), (i, 0, n))
    
    Eq << algebre.eq.imply.eq.invoke.apply(Eq[0], Product[i:n], simplify=False)

if __name__ == '__main__':
    prove(__file__)

