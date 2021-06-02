from util import *


import axiom


def doit(self):
    xi, *limits = self.args
    * limits, limit = limits
    i, a, b = axiom.limit_is_Interval((limit,))
    diff = b - a
    assert diff == int(diff)

    sgm = self.func.identity(xi)

    for t in range(diff):
        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, a + t) for c in ab)))

        sgm = self.func.operator(sgm, self.func(xi._subs(i, a + t), *_limits))
    return sgm


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
    f = Function.f(integer=True)

    n = 5
    Eq << apply(Sum[j:f(i), i:n](x[i, j]))

    s = Symbol.s(Lamda[i](Sum[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

from . import setlimit
