from axiom.utility import prove, apply
from sympy.core.relational import Equality, LessThan
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
    lhs, rhs = axiom.is_LessThan(given)
    assert lhs.is_nonnegative
    return LessThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True, nonnegative=True)
    g = Function.g(nargs=(), shape=(), real=True, nonnegative=True)
    
    Eq << apply(LessThan(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << algebre.forall_le.imply.le.product.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

