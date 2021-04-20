from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Greater(given)
    assert rhs.is_positive
    
    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)
    
    Eq << apply(Greater(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << algebra.forall_gt.imply.gt.product.apply(Eq[-1])


if __name__ == '__main__':
    prove()

