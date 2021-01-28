from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictLessThan
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_strict_less_than(given)
    lhs, rhs = eq.args
    assert lhs.is_positive
    
    return StrictLessThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(ForAll[i:n](StrictLessThan(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << algebre.forall_strict_greater_than.imply.strict_greater_than.product.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

