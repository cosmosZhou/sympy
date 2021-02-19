from sympy import *
from axiom.utility import prove, apply

from sympy.sets.conditionset import conditionset
from axiom import sets, discrete
from axiom.discrete.combinatorics.permutation import mapping


@apply
def apply(n, P_quote=None):
    Q, w, x = mapping.Qu2v.predefined_symbols(n)
    if P_quote is None:
        P_quote = Symbol("P'", definition=conditionset(x[:n + 1], Equality(x[:n].set_comprehension(), Interval(0, n - 1, integer=True)) & Equality(x[n], n)))
    
    return Equality(Q[n], P_quote)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq << sets.imply.forall.conditionset.apply(Eq[-1].lhs).split()
        
    Eq << Eq[-1].apply(discrete.combinatorics.permutation.pop_back.interval, Eq[-2])
    
    Eq.forall_P_quote = Eq[-1] & Eq[-3]
    
    Eq << sets.imply.forall.conditionset.apply(Eq[1].lhs).split()
    
    Eq << Eq[-1].apply(discrete.combinatorics.permutation.push_back, Eq[-2])
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << sets.forall.forall.imply.equal.apply(Eq.forall_P_quote, Eq[-1])


if __name__ == '__main__':
    prove(__file__)
