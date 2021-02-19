from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictLessThan
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
    lhs, rhs = axiom.is_StrictLessThan(given)
    assert lhs.is_positive
    
    return StrictLessThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(StrictLessThan(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (i, 0, n))
    
    Eq << algebre.forall_strict_less_than.imply.strict_less_than.product.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

