
from util import *

import axiom







@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_random 
    assert rhs.is_random
    return Equal(Probability(lhs), Probability(rhs))    


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    p = Symbol.p(shape=(n,), integer=True, random=True)
    q = Symbol.q(shape=(n,), integer=True, random=True)
    
    Eq << apply(Equal(p[i], q[i]))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

