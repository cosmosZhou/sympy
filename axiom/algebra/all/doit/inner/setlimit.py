from util import *


def doit(All, self):
    xi, (i, s), *limits = self.of(All)
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    for t in s.args:
        sgm = All.operator(sgm, xi._subs(i, t))

    assert limits
    return All(sgm, *limits)

@apply(given=None)
def apply(self):
    return Equivalent(self, doit(All, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(All[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Equivalent(All[i:m](Equal(Bool(All[j:{a, b, c, d}](x[i, j] > 0)), 1)), All[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Bool, All).apply(algebra.all.to.et.doit.setlimit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

