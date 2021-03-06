from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Product
from sympy.core.function import Function
import axiom
from sympy.sets.sets import Interval


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_equal(given)
    lhs, rhs = eq.args
    
    return Equality(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), complex=True)
    g = Function.g(nargs=(), shape=(), complex=True)
    
    Eq << apply(ForAll[i:n](Equality(f(i), g(i))))
    
    i_ = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0].subs(i, i_)
    
    Eq << Eq[1].this.lhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.lhs.subs(Eq[2])
    

if __name__ == '__main__':
    prove(__file__)

