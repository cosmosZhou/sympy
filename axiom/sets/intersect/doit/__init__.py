from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    xi, *limits = axiom.is_Sum(self)
    try:
        i, a, b = axiom.limit_is_Interval(limits)
    except:
        i = axiom.limit_is_symbol(limits)
        domain = xi.domain_defined(i)
        a, b = axiom.is_Interval(domain)
    
    diff = b - a
    assert diff == int(diff)
    
    sgm = ZeroMatrix(*xi.shape)
    for t in range(diff):
        sgm += xi._subs(i, a + t)
        
    return Equal(self, sgm)


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
     
    n = 5
    Eq << apply(Sum[i:n](x[i]))
    
    n -= 1
    Eq << Eq[-1].this.lhs.bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.bisect({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.bisect({n})


if __name__ == '__main__':
    prove()

from . import inner
