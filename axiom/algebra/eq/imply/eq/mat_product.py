from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equal(MatProduct(lhs, *limits).simplify(), MatProduct(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)
    
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].forall((i,))
    
    Eq << algebra.forall_eq.imply.eq.mat_product.apply(Eq[-1])


if __name__ == '__main__':
    prove()

