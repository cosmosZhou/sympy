from sympy import *
from axiom.utility import prove, apply
from axiom import sets, discrete, algebra
from axiom.discrete.combinatorics.permutation import mapping


@apply
def apply(n, P_quote=None):
    Q, w, x = mapping.Qu2v.predefined_symbols(n)
    if P_quote is None:
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].set_comprehension(), Interval(0, n - 1, integer=True)) & Equal(x[n], n)))
    
    return Equal(Q[n], P_quote)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq << sets.imply.forall.conditionset.apply(Eq[-1].lhs)
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])

    Eq << Eq[-3].this.function.apply(discrete.combinatorics.permutation.pop_back.interval)
    
    Eq.forall_P_quote = Eq[-1] & Eq[-3]
    
    Eq << sets.imply.forall.conditionset.apply(Eq[1].lhs)
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq << Eq[-3].this.function.apply(discrete.combinatorics.permutation.push_back)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << sets.forall.forall.imply.eq.apply(Eq.forall_P_quote, Eq[-1])


if __name__ == '__main__':
    prove()
