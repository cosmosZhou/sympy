from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.sets.sets import Interval
from sympy import Symbol
from sympy.functions.elementary.complexes import Abs
from axiom import sets
from axiom.discrete.combinatorics.permutation import mapping
from sympy.concrete.expr_with_limits import UNION, ForAll
from sympy.concrete.summations import Sum



@plausible
def apply(n, Q=None):
    if Q is None:
        Q, w, x = mapping.Qu2v.predefined_symbols(n)    

    t = Q.definition.variable
    return Equality(Abs(UNION[t](Q[t])), Sum[t](Abs(Q[t])))


from axiom.utility import check
from sympy import S


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Q = Eq[0].lhs.base
    t = Q.definition.variable
    j = Symbol.j(integer=True)
    
    Eq.nonoverlapping = ForAll[j: Interval(0, n, integer=True) - t.set, t](Equality(Q[t] & Q[j], Q[t].etype.emptySet), plausible=True)
    
    Eq << ~Eq.nonoverlapping
    
    Eq << Eq[-1].apply(sets.is_nonemptyset.imply.exists_contains.overlapping, wrt=Eq[0].rhs.variable, domain=Q[t], simplify=None)
    
    Eq.Qj_definition = Q[j].this.definition
    
    Eq << Eq[-1].subs(Eq.Qj_definition)
    
    Eq << Eq[-1].split()[0]
    
    Eq << sets.imply.conditionset.apply(Q[t]).split()[0]
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << sets.forall_equality.imply.equality.nonoverlapping.apply(Eq.nonoverlapping)    

    
if __name__ == '__main__':
    prove(__file__)
