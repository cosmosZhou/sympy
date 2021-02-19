from axiom.utility import prove, apply
from sympy.core.relational import Equality, GreaterThan
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_GreaterThan(given)
    assert rhs.is_nonnegative
    
    return GreaterThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True, nonnegative=True)
    g = Function.g(nargs=(), shape=(), real=True, nonnegative=True)
    
    Eq << apply(GreaterThan(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (i, 0, n))
    
    Eq << algebre.forall_greater_than.imply.greater_than.product.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

