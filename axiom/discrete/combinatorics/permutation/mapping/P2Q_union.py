from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.sets.sets import Interval
from sympy import Symbol
from axiom import sets
from axiom.discrete.combinatorics.permutation import mapping
from sympy import UNION
from sympy.sets.conditionset import conditionset
from sympy.sets.contains import Subset


@plausible
def apply(n):
    Q, w, x = mapping.Qu2v.predefined_symbols(n)    
    
    Pn1 = Symbol("P_{n+1}", definition=conditionset(x[:n + 1], Equality(x[:n + 1].set_comprehension(), Interval(0, n, integer=True))))

    t = Q.definition.variable
    return Equality(UNION[t](Q[t]), Pn1)


from axiom.utility import check
from sympy import S


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Q = Eq[0].lhs.base
    t = Q.definition.variable
    
    Eq << Subset(Eq[0].lhs, Eq[2].rhs, plausible=True)
    
    Eq.subset_P = sets.subset.imply.subset.apply(Eq[-1], (t,), simplify=False)
    
    Eq.subset_Q = Subset(Eq.subset_P.rhs, Eq.subset_P.lhs, plausible=True)
    
    Eq << Eq.subset_Q.definition
    
    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[0].rhs.variable)    
    
    Eq << Eq[-1].definition
    
    Eq << Eq[-1].definition
    
    Eq << sets.imply.forall.conditionset.apply(Eq[2].rhs)

    Eq <<= Eq.subset_P & Eq.subset_Q    
if __name__ == '__main__':
    prove(__file__)
