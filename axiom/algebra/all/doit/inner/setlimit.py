from util import *


import axiom


def doit(self):
    xi, *limits = self.args
    limit, *limits = limits
    i, s = axiom.limit_is_set((limit,))
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    for t in s.args:
        sgm = self.func.operator(sgm, xi._subs(i, t))

    assert limits
    return self.func(sgm, *limits)

@apply(given=None)
def apply(self):
    assert self.is_ForAll
    return Equivalent(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(ForAll[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Equivalent(ForAll[i:m](Equal(Bool(ForAll[j:{a, b, c, d}](x[i, j] > 0)), 1)), ForAll[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Bool, ForAll).apply(algebra.all.to.et.doit.setlimit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

