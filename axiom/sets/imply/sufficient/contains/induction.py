from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply(given=None)
def apply(given, n):
    x, Ak = axiom.is_Contains(given)
    A, k = axiom.is_Indexed(Ak)
    
    return Sufficient(ForAll[k:n](Contains(x, A[k])), Contains(x, INTERSECTION[k:n](A[k])))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(Contains(x, A[k]), n)
    
    Eq.initial = Eq[0].subs(n, 1)

    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << algebra.sufficient.imply.sufficient.et.both_sided.apply(Eq[0], cond=Contains(x, A[n]))
    
    Eq << Eq[-1].this.lhs.apply(algebra.et.given.forall.absorb.back)
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

