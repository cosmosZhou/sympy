from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_supset(given)
    lhs, rhs = eq.args
    
    return Supset(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Supset(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << sets.forall_subset.imply.subset.union_comprehension.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

