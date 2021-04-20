from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(n, P_quote=None):    
    
    if P_quote is None:
        x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].set_comprehension(), Interval(0, n - 1, integer=True)) & Equal(x[n], n)))
    else:
        x = P_quote.definition.variable.base
    
    P = Symbol.P(conditionset(x[:n], Equal(x[:n].set_comprehension(), Interval(0, n - 1, integer=True))))    
    return Equal(Abs(P), Abs(P_quote))


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    P_quote = Eq[1].lhs
    
    i = Symbol.i(integer=True)
    
    x_quote = Symbol("x'", LAMBDA[i:n + 1](Piecewise((n, Equal(i, n)), (x[i], True))))
    Eq.x_quote_definition = x_quote.this.definition
    
    Eq << Eq.x_quote_definition[:n]
    
    Eq.mapping = Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq.x_quote_definition[i]
    
    Eq << sets.eq.imply.eq.set_comprehension.apply(Eq[-1], (i, 0, n))
    
    Eq.x_quote_n_definition = Eq[-2].subs(i, n)
    
    Eq << sets.imply.forall.conditionset.apply(P)
    
    Eq << algebra.forall_eq.cond.imply.forall.subs.apply(Eq[-1], Eq[-2])
    
    Eq.P2P_quote = ForAll[x[:n]:P](Contains(x_quote, P_quote), plausible=True)
    
    Eq << Eq.P2P_quote.this.function.rhs.definition
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << sets.imply.forall.conditionset.apply(P_quote)
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq.x_quote_n_definition, Eq[-2], simplify=False)
    
    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.transit)
    
    Eq.mapping_quote = ForAll[x[:n + 1]:P_quote](Equal(x_quote, x[:n + 1]), plausible=True)
    
    Eq << Eq.mapping_quote.this.function.apply(algebra.eq.given.et.split.block_matrix, Slice[-1:])
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.mapping)
    
    Eq << ForAll[x[:n + 1]:P_quote](Contains(x[:n], P), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << sets.forall_contains.forall_contains.forall_eq.forall_eq.imply.eq.apply(Eq[-1], Eq.P2P_quote, Eq.mapping_quote, Eq.mapping)
    
    Eq << Eq[-1].reversed

        
if __name__ == '__main__':
    prove()
