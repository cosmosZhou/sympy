from util import *


@apply
def apply(self):
    (_xi, xi), limit = self.of(Sum[Expr - Expr])
    try:        
        i, a, b = limit
    except:
        (i,) = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    assert i.is_integer
    
    assert _xi == xi._subs(i, i + 1)
    return Equal(self, xi._subs(i, b) - xi._subs(i, a), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(Sum[i:n + 1](x[i + 1] - x[i]))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    #https://en.wikipedia.org/wiki/Telescoping_series


if __name__ == '__main__':
    run()
from . import offset
