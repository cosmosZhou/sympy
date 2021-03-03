from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_equal(given)
    lhs, rhs = eq.args
    
    return Equality(UNION(FiniteSet(lhs), *limits).simplify(), UNION(FiniteSet(rhs), *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Symbol.f(shape=(oo,), etype=dtype.integer)
    g = Symbol.g(shape=(oo,), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Equality(f[i], g[i])))
    
    Eq << Eq[0].apply(sets.equal.imply.equal.set, simplify=False)
    
    Eq << sets.forall_equal.imply.equal.union.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

