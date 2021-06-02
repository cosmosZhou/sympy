from util import *

import axiom

from axiom.discrete.K.to.add.definition import K
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given, n): 
    xj, *limits = axiom.all_is_positive(given)
    j, a, o = axiom.limit_is_Interval(limits)
    assert o == oo
    assert a == 1
    x, _j = xj.of(Indexed)
    assert _j == j
    assert n > 0
    return Less(alpha(x[:2 * n - 1]), alpha(x[:2 * n + 1]))


@prove(surmountable=False)
def prove(Eq): 
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(ForAll[i:1:oo](x[i] > 0), n)
    return
    Eq << discrete.imply.suffice.is_positive.K.apply(x[:n])
    
    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    run()

