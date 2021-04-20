from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_subset(given)
    lhs, rhs = eq.args
    
    return Subset(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Subset(f(i), g(i))))
    
    Eq << sets.imply.sufficient.subset.induction.apply(Subset(f(i), g(i)), (i, 0, n))
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove()

from . import lhs