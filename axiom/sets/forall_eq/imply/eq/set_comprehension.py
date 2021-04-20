from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_eq(given)
    lhs, rhs = eq.args
    
    return Equal(UNION(FiniteSet(lhs), *limits).simplify(), UNION(FiniteSet(rhs), *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Symbol.f(shape=(oo,), etype=dtype.integer)
    g = Symbol.g(shape=(oo,), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Equal(f[i], g[i])))
    
    Eq << Eq[0].this.function.apply(sets.eq.imply.eq.set, simplify=False)
    
    Eq << sets.forall_eq.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    prove()

