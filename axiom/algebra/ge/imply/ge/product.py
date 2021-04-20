from axiom.utility import prove, apply
from sympy.core.relational import Equal, GreaterEqual
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebra, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_GreaterEqual(given)
    assert rhs.is_nonnegative
    
    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(shape=(), real=True, nonnegative=True)
    g = Function.g(shape=(), real=True, nonnegative=True)
    
    Eq << apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << algebra.forall_ge.imply.ge.product.apply(Eq[-1])


if __name__ == '__main__':
    prove()

