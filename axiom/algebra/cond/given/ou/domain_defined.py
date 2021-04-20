from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import sets, algebra

    
@apply
def apply(imply, wrt=None):
    cond = imply.domain_defined(wrt)    
    return Or(imply, NotContains(wrt, cond))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True, given=True)
    
    x = Symbol.x(shape=(n,), real=True, given=True)
    
    Eq << apply(x[i] > 0, wrt=i)
    
    Eq << algebra.ou.imply.forall.apply(Eq[1], pivot=0)
    
        
if __name__ == '__main__':
    prove()

