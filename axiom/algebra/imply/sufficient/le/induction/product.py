from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply(given=None)
def apply(given, *limits): 
    xk, yk = axiom.is_LessEqual(given)
    k, a, b = axiom.limit_is_Interval(limits)
    assert xk._has(k)
    assert yk._has(k)
    assert xk >= 0
    
    return Sufficient(ForAll[k:a:b](xk <= yk), Product[k:a:b](xk) <= Product[k:a:b](yk))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    
    y = Symbol.y(shape=(oo,), integer=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)

    Eq << apply(x[k] <= y[k], (k, 0, n))
    
    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << algebra.sufficient.imply.sufficient.et.both_sided.apply(Eq[0], cond=x[n] <= y[n])
    
    Eq << Eq[-1].this.lhs.apply(algebra.et.given.forall.absorb.back)
    
    Eq << Eq[-1].this.rhs.apply(algebra.le.le.imply.le.product.absorb.back)    
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

