from sympy import *
from axiom.utility import prove, apply
from sympy.sets.conditionset import conditionset
from axiom import discrete, algebre


@apply(imply=True)
def apply(n):
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    
    return Equality(abs(conditionset(x[:n], Equality(x[:n].set_comprehension(), Interval(0, n - 1, integer=True)))), factorial(n))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq.initial = Eq[-1].subs(n, 1)
    
    Eq << Eq.initial.this.lhs.arg.limits[0][1].simplify()
    
    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << discrete.combinatorics.permutation.mapping.P2Q_union.apply(n)
    
    Q = Eq[-1].lhs.function.base
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)
    
    Eq << discrete.combinatorics.permutation.nonoverlapping.apply(n, Q=Q)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << discrete.combinatorics.permutation.mapping.inbetween.apply(n, Q=Q)    
    
    P_quote = Eq[-1].rhs.arg
    Eq << Eq[-2].subs(Eq[-1])
    Eq << discrete.combinatorics.permutation.mapping.last.apply(n, P_quote=P_quote)
    
    Eq.P_definition = Eq[-1].lhs.arg.this.definition
    
    Eq.recursion = Eq[-2].subs(Eq[-1].reversed)
    
    Eq.Pn1_definition = Eq.recursion.lhs.arg.this.definition
    
    Eq << Eq[0].subs(Eq.P_definition.reversed)

    Eq << Eq.induction.subs(Eq.Pn1_definition.reversed)
    
    Eq << Eq.recursion.subs(Eq[-1], Eq[-2])
    
    Eq << discrete.combinatorics.permutation.factorial.expand.apply(n + 1)
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.initial, Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove(__file__)

