from util import *


def doit(self):
    xi, limit = self.args
    try:
        import axiom
        i, a, b = axiom.limit_is_Interval((limit,))
    except:
        (i,) = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    diff = b - a
    assert diff == int(diff)

    sgm = self.func.identity(xi)
    for t in range(diff):
        sgm = self.func.operator(sgm, xi._subs(i, a + t))

    return sgm


@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)

    n = 5
    Eq << apply(Sum[i:n](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, cond={n})


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
