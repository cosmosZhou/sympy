from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_equal(given)
    lhs, rhs = eq.args
    
    return Equality(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), etype=dtype.integer)
    g = Function.g(nargs=(), shape=(), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Equality(f(i), g(i))))
    
    m = Symbol.m(domain=Interval(1, n - 1, integer=True))
    Eq.hypothesis = Eq[1]._subs(n, m).copy(plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(m, 1)
    
    Eq << Eq[0].subs(i, 0)
    
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    Eq << Eq[0].subs(i, m)
    
    Eq << Eq.hypothesis.apply(sets.equal.imply.equal.union, Eq[-1].lhs)
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.initial, Eq[-1], n=m, start=1)
    
    Eq << Eq.hypothesis.subs(m, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)
    

if __name__ == '__main__':
    prove(__file__)

