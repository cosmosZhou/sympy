from util import *


import axiom


def doit(self):
    xi, *limits = self.args
    * limits, limit = limits
    assert limits
    i, s = axiom.limit_is_set((limit,))
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    for t in s.args:
        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, t) for c in ab)))

        sgm = self.func.operator(sgm, self.func(xi._subs(i, t), *_limits))

    return sgm


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
    f = Function.f(integer=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(ForAll[j:f(i), i:{a, b, c, d}](x[i, j] > 0))

    Eq << Equivalent(ForAll[j:f(i), i:{a}](x[i, j] > 0), ForAll[j:f(a)](x[a, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.all.doit.outer.setlimit)

    Eq << Equivalent(ForAll[j:f(i), i:{b}](x[i, j] > 0), ForAll[j:f(b)](x[b, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.all.doit.outer.setlimit)

    Eq << algebra.equivalent.equivalent.imply.equivalent.et.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(ForAll[j:f(i), i:{c}](x[i, j] > 0), ForAll[j:f(c)](x[c, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.all.doit.outer.setlimit)

    Eq << algebra.equivalent.equivalent.imply.equivalent.et.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(ForAll[j:f(i), i:{d}](x[i, j] > 0), ForAll[j:f(d)](x[d, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.all.doit.outer.setlimit)

    Eq << algebra.equivalent.equivalent.imply.equivalent.et.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()

