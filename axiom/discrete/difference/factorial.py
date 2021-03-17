from sympy import *
from axiom.utility import prove, apply
from axiom import discrete, algebre


@apply
def apply(x, n):
    if not x.is_Symbol:
        return
    return Equality(Difference(x ** n, x, n), factorial(n))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    k = Symbol.k(integer=True, nonnegative=True)
    t = x ** k
    assert t.is_complex
    assert t.is_extended_real
    
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(x, n)
    
    Eq.initial = Eq[0].subs(n, 0)
    
    Eq << Eq.initial.doit()
    
    Eq.induction = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induction.this.lhs.bisect(Slice[:1])

    Eq << Eq[-1].this.lhs.expr.doit()
    
    Eq << discrete.combinatorics.binomial.theorem.apply(x, 1, n + 1) - x ** (n + 1)

    Eq << Eq[-1].this.rhs.args[1].bisect(Slice[-1:])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.astype(Sum)

    Eq << Eq[-1].this.lhs.bisect(n.set)
    
    Eq << discrete.combinatorics.permutation.factorial.expand.apply(n + 1)
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    _k = Symbol.k(domain=Interval(0, n, right_open=True, integer=True))
    
    Eq << Eq[0].subs(n, _k)
    
    Eq << Difference(Eq[-1], x, n - _k)
    Eq << Eq[-1].this.lhs.as_one_term()
        
    Eq << Eq[-1] * binomial(n + 1, _k)
    
    Eq << Eq[-1].apply(algebre.eq.imply.eq.sum, (_k,))    
    
    Eq << Eq[-1].this.lhs.limits_subs(_k, k)
    
    Eq << Eq[0] * (n + 1)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq.induction.induct()

    Eq << Eq[-1].this.lhs.forall((_k,))
    
    Eq << algebre.eq.sufficient.imply.eq.second.induction.having.forall.apply(Eq.initial, Eq[-1], n=n)
    
    Eq << Eq[0].subs(n, _k)
    

if __name__ == '__main__':
    prove(__file__)

