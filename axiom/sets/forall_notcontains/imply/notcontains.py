from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(given):
    notcontains, *limits = axiom.forall_notcontains(given)
    
    e, S = notcontains.args
    
    return NotContains(e, UNION(S, *limits))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(ForAll[k:n](NotContains(x, A[k])))

    m = Symbol.m(domain=Interval(1, n - 1, integer=True))
    Eq.hypothesis = Eq[1]._subs(n, m).copy(plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(m, 1)
    
    Eq << Eq[0].subs(k, 0)
    
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    Eq << Eq[0].subs(k, m)

    Eq << Eq.hypothesis.apply(sets.notcontains.notcontains.imply.notcontains.union, Eq[-1])
        
    Eq << Eq.induction.induct()
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=m, start=1)

    Eq << Eq.hypothesis.subs(m, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)

    
if __name__ == '__main__':
    prove(__file__)

