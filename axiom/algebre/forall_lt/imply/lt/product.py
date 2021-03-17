from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
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
    
    Eq << algebre.forall_gt.imply.gt.product.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

