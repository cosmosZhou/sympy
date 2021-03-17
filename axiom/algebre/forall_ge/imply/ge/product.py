from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_greater_than(given)
    lhs, rhs = eq.args
    assert rhs.is_nonnegative
    
    return GreaterThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), real=True, nonnegative=True)
    g = Function.g(nargs=(), shape=(), real=True, nonnegative=True)
    
    Eq << apply(ForAll[i:n](GreaterThan(f(i), g(i))))
    
    m = Symbol.m(domain=Interval(1, n - 1, integer=True))
    Eq.hypothesis = Eq[1]._subs(n, m).copy(plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(m, 1)
    
    Eq << Eq[0].subs(i, 0)
    
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    Eq << Eq[0].subs(i, m)
    
#     assert Eq.hypothesis.lhs.is_extended_real
#     assert Eq.hypothesis.lhs.is_extended_negative is False
#     assert Eq.hypothesis.lhs.is_extended_nonnegative
#     assert Eq.hypothesis.lhs.is_nonnegative
#     assert Eq[-1].lhs.is_nonnegative
    Eq << Eq.hypothesis * Eq[-1]
    
    Eq << Eq[-1].this.lhs.astype(Product)
    
    Eq << Eq[-1].this.rhs.astype(Product)
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=m, start=1)
    
    Eq << Eq.hypothesis.subs(m, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)
    

if __name__ == '__main__':
    prove(__file__)

