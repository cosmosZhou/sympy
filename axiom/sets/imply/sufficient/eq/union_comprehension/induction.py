from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply(given=None)
def apply(given, *limits):
    fk, gk = axiom.is_Equal(given)
    k, a, b = axiom.limit_is_Interval(limits)
    
    return Sufficient(ForAll[k:a:b](Equal(fk, gk)), Equal(UNION[k:a:b](fk), UNION[k:a:b](gk)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)
    
    Eq << apply(Equal(f(k), g(k)), (k, 0, n))
    
    Eq.initial = Eq[0].subs(n, 1)

    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << algebra.sufficient.imply.sufficient.et.both_sided.apply(Eq[0], cond=Equal(f(n), g(n)))
        
    Eq << Eq[-1].this.rhs.apply(sets.eq.eq.imply.eq.union_comprehension.absorb.back)
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

