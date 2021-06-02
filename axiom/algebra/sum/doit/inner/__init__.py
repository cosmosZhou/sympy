from util import *


import axiom


def doit(self):
    xi, *limits = self.args
    limit, *limits = limits
    i, a, b = axiom.limit_is_Interval((limit,))
    diff = b - a
    assert diff == int(diff)

    sgm = self.func.identity(xi)
    for t in range(diff):
        sgm = self.func.operator(sgm, xi._subs(i, a + t))

    return self.func(sgm, *limits)


@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)

    n = 5
    Eq << apply(Sum[j:n, i:m](x[i, j]))

    s = Symbol.s(Lamda[i](Sum[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

from . import setlimit
