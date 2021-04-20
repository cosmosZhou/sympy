from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given, index=0):
    print('this theorem should be generalized', __file__)
    sgm = axiom.is_nonnegative(given)
    function, *limits = axiom.is_Sum(sgm)
    del limits[index]
    return GreaterEqual(Sum(function, *limits), 0)


@prove
def prove(Eq):
    f = Function.f(real=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(Sum[i:n, j:n](f(i, j)) >= 0)
    
    Eq << algebra.ge.imply.ge.sum.apply(Eq[1], (i, 0, n))
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap)
    
    
if __name__ == '__main__':
    prove()
