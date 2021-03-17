from sympy import *
from axiom.utility import prove, apply
from axiom import discrete, algebre, calculus, sets
import axiom


def is_catalan_series(*given):
    C0_definition, Cn1_definition = given
    
    C0, one = axiom.is_Equal(C0_definition)
    assert one.is_One
    
    Cn1, summation = axiom.is_Equal(Cn1_definition)
    fk, (k, zero, n1) = axiom.is_Sum(summation)
    
    n = n1 - 1
    assert zero.is_zero
    
    Cn = Cn1._subs(n, n - 1)
    assert Cn._subs(n, 0) == C0

    Cnk, Ck = axiom.is_Times(fk)
    assert Ck == Cn._subs(n, k)
    assert Cnk == Cn._subs(n, n - k)
    return Cn, n

    
@apply
def apply(*given):
    Cn, n = is_catalan_series(*given)
    return StrictGreaterThan(Cn, 0)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    
    C = Symbol.C(shape=(oo,), integer=True)
    
    Eq << apply(Equality(C[0], 1),
                Equality(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))
    
    Eq.initial = algebre.eq.imply.gt.apply(Eq[0], 0)
    
    k = Symbol.k(domain=Interval(0, n, integer=True))
    
    Eq.hypothsis_n1 = Eq[2].subs(n, n + 1)
    
    Eq.hypothsis_k = Eq[2].subs(n, k)
    
    Eq.hypothsis_nk = Eq.hypothsis_k.subs(k, n - k)
    
    Eq << Eq.hypothsis_nk * Eq.hypothsis_k
    
    Eq << algebre.gt.imply.gt.sum.apply(Eq[-1], (k,))

    Eq << Eq[-1].this.lhs.limits_subs(k, k.copy(domain=None))
    
    Eq << Eq[-1].this.lhs.subs(Eq[1].reversed)        
    
    Eq << Eq.hypothsis_n1.induct()
    
if __name__ == '__main__':
    prove(__file__)


