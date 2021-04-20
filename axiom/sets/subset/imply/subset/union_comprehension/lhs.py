from axiom.utility import prove, apply
from sympy import *
from axiom import algebra, sets


@apply
def apply(given, *limits):
    assert given.is_Subset
    fx, A = given.args
    
    return Subset(UNION(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)
   
    Eq << apply(Subset(x[i], A), (i, 0, m))
    
    Eq << algebra.cond.imply.forall.restrict.apply(Eq[0], (i, 0, m))
    
    Eq << sets.forall_subset.imply.subset.union_comprehension.apply(Eq[-1])    

    
if __name__ == '__main__':
    prove()

