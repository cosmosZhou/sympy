from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply(given=None)
def apply(given, *limits):
    fk, A = axiom.is_Subset(given)
    k, a, b = axiom.limit_is_Interval(limits)
    assert not A._has(k)
    return Sufficient(ForAll[k:a:b](Subset(fk, A)), Subset(UNION[k:a:b](fk), A))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(Subset(f(k), A), (k, 0, n))
    
    Eq.initial = Eq[0].subs(n, 1)

    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << algebra.sufficient.imply.sufficient.et.both_sided.apply(Eq[0], cond=Subset(f(n), A))
        
    Eq << Eq[-1].this.lhs.apply(algebra.et.given.forall.absorb.back)

    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

