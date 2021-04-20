from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra


@apply
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p[:n]:P](Exists[i:n](Equal(p[i], n - 1)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq << Eq[1].subs(Eq[0])
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq[-1].limits)
    
    Eq << Contains(n - 1, Eq[-1].rhs, plausible=True)
    
    Eq << algebra.forall_eq.cond.imply.forall.subs.apply(Eq[-2].reversed, Eq[-1])
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.exists_contains.st.union_comprehension)
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()
