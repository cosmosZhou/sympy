from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_ge(given)
    lhs, rhs = eq.args
    assert rhs.is_nonnegative
    
    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True, nonnegative=True)
    g = Function.g(shape=(), real=True, nonnegative=True)
    
    Eq << apply(ForAll[i:n](GreaterEqual(f(i), g(i))))
    
    Eq << algebra.imply.sufficient.ge.induction.product.apply(GreaterEqual(f(i), g(i)), (i, 0, n))

    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

if __name__ == '__main__':
    prove()

