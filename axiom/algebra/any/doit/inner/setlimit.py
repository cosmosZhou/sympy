from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.all.doit.inner.setlimit import doit
    return Equivalent(self, doit(Any, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Any[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Equivalent(Any[i:m](Equal(Bool(Any[j:{a, b, c, d}](x[i, j] > 0)), 1)), Any[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Bool, Any).apply(algebra.any.to.ou.doit.setlimit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-02-10
