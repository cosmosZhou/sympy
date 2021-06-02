from util import *


import axiom


def doit(self):
    xi, *limits = self.args
    limit, *limits = limits
    i, s = axiom.limit_is_set((limit,))
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    while s:
        t, *args = s.args
        sgm = self.func.operator(sgm, xi._subs(i, t))

        s = FiniteSet(*args)
        assert Contains(t, s).is_BooleanFalse

    assert limits
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

    Eq << apply(Sum[j:{0, 1, 2, 3}, i:m](x[i, j]))

    s = Symbol.s(Lamda[i](Sum[j:{0, 1, 2, 3}](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

