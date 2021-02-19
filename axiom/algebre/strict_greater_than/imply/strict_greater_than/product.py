from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan
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
    lhs, rhs = axiom.is_StrictGreaterThan(given)
    assert rhs.is_positive
    
    return StrictGreaterThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(StrictGreaterThan(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (i, 0, n))
    
    Eq << algebre.forall_strict_greater_than.imply.strict_greater_than.product.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

