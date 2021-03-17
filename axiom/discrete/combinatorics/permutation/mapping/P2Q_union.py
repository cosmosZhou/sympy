from axiom.utility import prove, apply

from sympy import *

from axiom.discrete.combinatorics.permutation import mapping
from axiom import sets


@apply
def apply(n):
    Q, w, x = mapping.Qu2v.predefined_symbols(n)    
    
    Pn1 = Symbol("P_{n+1}", conditionset(x[:n + 1], Equality(x[:n + 1].set_comprehension(), Interval(0, n, integer=True))))

    t = Q.definition.variable
    return Equality(UNION[t](Q[t]), Pn1)


from sympy import S


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Q = Eq[0].lhs.base
    t = Q.definition.variable
    
    Eq << Subset(Eq[0].lhs, Eq[2].rhs, plausible=True)
    
    Eq.subset_P = sets.subset.imply.subset.union_comprehension.lhs.apply(Eq[-1], (t,), simplify=False)
    
    Eq.subset_Q = Subset(Eq.subset_P.rhs, Eq.subset_P.lhs, plausible=True)
    
    Eq << sets.subset.given.forall_contains.apply(Eq.subset_Q)
    
    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[0].rhs.variable)    
    
    Eq << Eq[-1].apply(sets.contains.given.exists_contains.having.union_comprehension)
    
    Eq << Eq[-1].this.function.function.rhs.definition
    
    Eq << sets.imply.forall.conditionset.apply(Eq[2].rhs)

    Eq <<= Eq.subset_P & Eq.subset_Q    
    
if __name__ == '__main__':
    prove(__file__)
