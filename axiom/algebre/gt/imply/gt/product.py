from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


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

    Eq << Eq[0].apply(algebre.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << algebre.forall_gt.imply.gt.product.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

