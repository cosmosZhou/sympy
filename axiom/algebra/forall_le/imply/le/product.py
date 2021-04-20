from axiom.utility import prove, apply
from sympy.core.relational import Equal, LessEqual
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebra, sets
from sympy.core.symbol import dtype


@apply
def apply(given):
    eq, *limits = axiom.forall_le(given)
    lhs, rhs = eq.args
    assert lhs.is_nonnegative
    
    return LessEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, nonnegative=True)
    g = Function.g(shape=(), real=True, nonnegative=True)
    
    Eq << apply(ForAll[i:n](LessEqual(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << algebra.forall_ge.imply.ge.product.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

