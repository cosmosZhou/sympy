from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_lt(given)
    lhs, rhs = eq.args
    assert lhs.is_positive
    
    return Less(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)
    
    Eq << apply(ForAll[i:n](Less(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << algebra.forall_gt.imply.gt.product.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

