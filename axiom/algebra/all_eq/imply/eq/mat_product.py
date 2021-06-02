from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Equal])
    
    return Equal(MatProduct(lhs, *limits).simplify(), MatProduct(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(m, m), complex=True)
    g = Function.g(shape=(m, m), complex=True)
    
    Eq << apply(ForAll[i:n](Equal(f(i), g(i))))
    
    i_ = Symbol.i(domain=Range(0, n))
    
    Eq << Eq[0].limits_subs(i, i_)
    
    Eq << Eq[1].this.lhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()

