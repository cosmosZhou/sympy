from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from axiom import discrete, algebre


@apply
def apply(n, k):
    assert k < n
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(domain=Interval(1, n - 1, integer=True))    
    Eq << apply(n, k)

    Eq.stirling2 = Eq[0].lhs.this.definition
    Eq.stirling0 = Eq[0].rhs.args[1].this.definition
    Eq.stirling1 = Eq[0].rhs.args[0].args[1].this.definition

    s2 = Symbol.s2(Eq.stirling2.rhs.arg)
    Eq << s2.this.definition
    
    Eq.stirling2 = Eq.stirling2.subs(Eq[-1].reversed)

    s0 = Symbol.s0(Eq.stirling0.rhs.arg)
    Eq << s0.this.definition
    
    Eq.stirling0 = Eq.stirling0.subs(Eq[-1].reversed)

    s1 = Symbol.s1(Eq.stirling1.rhs.arg)
    Eq << s1.this.definition
     
    Eq.stirling1 = Eq.stirling1.subs(Eq[-1].reversed)
    e = Symbol.e(etype=dtype.integer.set)

    Eq << s2.this.bisect(conditionset(e, Contains({n}, e), s2))

    Eq.s2_abs = Eq[-1].apply(algebre.eq.imply.eq.abs)    

    Eq.s2_abs_plausible = Eq[0].subs(Eq.stirling2, Eq.stirling0, Eq.stirling1)

    Eq << discrete.combinatorics.stirling.second.mapping.s2_A.apply(n, k, s2)
    
    A = Eq[-1].rhs.function.base

    Eq << discrete.combinatorics.stirling.second.mapping.s2_B.apply(n, k, s2)
    B = Eq[-1].rhs

    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq << discrete.combinatorics.stirling.second.mapping.s0_B.apply(n, k, s0, B)

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1])

    Eq << discrete.combinatorics.stirling.second.nonoverlapping.A.apply(n, k, A)

    Eq << Eq.A_union_abs.subs(Eq[-1])
    
    Eq << discrete.combinatorics.stirling.second.mapping.s1_Aj.apply(n, k, s1, A).reversed

    Eq << Eq[-1].apply(algebre.eq.imply.eq.sum, *Eq[-2].lhs.limits)    


if __name__ == '__main__':
    prove(__file__)

