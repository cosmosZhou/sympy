from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Subset(given)
    
    return Subset(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(shape=(), etype=dtype.real)
    g = Function.g(shape=(), etype=dtype.real)
    
    Eq << apply(Subset(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << sets.forall_subset.imply.subset.union_comprehension.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    prove()

