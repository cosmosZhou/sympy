from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_gt(given)
    lhs, rhs = eq.args
    assert rhs.is_positive
    
    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)
    
    Eq << apply(ForAll[i:n](Greater(f(i), g(i))))
    
    Eq << algebra.imply.sufficient.gt.induction.product.apply(f(i) > g(i), (i, 0, n))
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove()

