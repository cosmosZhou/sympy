from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
from axiom.discrete.combinatorics.permutation import mapping


@apply
def apply(n, Q=None):
    if Q is None:
        Q, w, x = mapping.Qu2v.predefined_symbols(n)    

    t = Q.definition.variable
    return Equality(Abs(UNION[t](Q[t])), Sum[t](Abs(Q[t])))


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Q = Eq[0].lhs.base
    t = Q.definition.variable
    j = Symbol.j(integer=True)
    
    Eq.nonoverlapping = ForAll[j: Interval(0, n, integer=True) // {t}, t](Equality(Q[t] & Q[j], Q[t].etype.emptySet), plausible=True)
    
    Eq << ~Eq.nonoverlapping
    
    Eq << Eq[-1].apply(sets.is_nonemptyset.imply.exists_contains.setlimit, wrt=Eq[0].rhs.variable, domain=Q[t], simplify=None)
    
    Eq.Qj_definition = Q[j].this.definition
    
    Eq << Eq[-1].subs(Eq.Qj_definition)
    
    Eq << algebre.exists_et.imply.exists.split.apply(Eq[-1], index=0)
    
    Eq << sets.imply.forall.conditionset.apply(Q[t])
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[-1], index=0)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << sets.forall_is_emptyset.imply.eq.nonoverlapping.setlimit.apply(Eq.nonoverlapping)    

    
if __name__ == '__main__':
    prove(__file__)
