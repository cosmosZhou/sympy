from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    eq, *limits = axiom.forall_eq(given)
    lhs, rhs = eq.args
    
    return Equal(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)
    
    Eq << apply(ForAll[i:n](Equal(f(i), g(i))))
    
    i_ = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << algebra.forall.imply.cond.subs.apply(Eq[0], i, i_)
    
    Eq << Eq[1].this.lhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.lhs.subs(Eq[2])
    

if __name__ == '__main__':
    prove()

