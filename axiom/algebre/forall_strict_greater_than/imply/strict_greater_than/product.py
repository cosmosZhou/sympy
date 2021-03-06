from axiom.utility import prove, apply
from sympy.core.relational import Equality, StrictGreaterThan
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_strict_greater_than(given)
    lhs, rhs = eq.args
    assert rhs.is_positive
    
    return StrictGreaterThan(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), real=True, positive=True)
    g = Function.g(nargs=(), shape=(), real=True, positive=True)
    
    Eq << apply(ForAll[i:n](StrictGreaterThan(f(i), g(i))))
    
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
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq.initial, Eq[-1], n=m, start=1)
    
    Eq << Eq.hypothesis.subs(m, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)
    

if __name__ == '__main__':
    prove(__file__)

