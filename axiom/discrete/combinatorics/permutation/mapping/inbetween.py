from sympy import *
from axiom.utility import prove, apply
from axiom import discrete, sets
from axiom.discrete.combinatorics.permutation import mapping


@apply
def apply(n, Q=None):
    if Q is None:
        Q, w, x = mapping.Qu2v.predefined_symbols(n)
    else:
        x = Q.definition.function.variable
    P_quote = Symbol("P'", conditionset(x[:n + 1], Equality(x[:n].set_comprehension(), Interval(0, n - 1, integer=True)) & Equality(x[n], n)))
    
    t = Q.definition.variable
    return Equality(Abs(Q[t]), Abs(P_quote))




@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq << discrete.combinatorics.permutation.mapping.identity_Qn.apply(n)
    
    Eq << Eq[2].subs(Eq[-1].reversed)
    
    u = Eq[-1].lhs.arg.indices[0]
    Eq << mapping.Qu2v.apply(n, n, u)
    
    Eq << mapping.Qu2v.apply(n, u, n)
    
    Eq << sets.forall_et.forall_et.imply.equal.apply(Eq[-1], Eq[-2])
    
    
if __name__ == '__main__':
    prove(__file__)
