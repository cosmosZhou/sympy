from sympy import *

from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom


@apply
def apply(given):
    subset, *limits = axiom.forall_subset(given)

    fx, A = subset.args
    
    return Subset(UNION(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)
   
    Eq << apply(ForAll[i:0:m](Subset(x[i], A)))
    
if __name__ == '__main__':
    prove(__file__)

