from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit
    return Equivalent(self, doit(Any, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a = Symbol(integer=True)
    f = Function(integer=True)
    g = Function(etype=dtype.integer)


    Eq << apply(Any[i:g(i), j:f(i, j) > 0, i:{a}](x[i, j] > 0))

    Eq << Equivalent(Any[i:{a}](Equal(Bool(Any[i:g(i), j:f(i, j) > 0](x[i, j] > 0)), 1)),
                     Any[i:g(i), j:f(i, j) > 0, i:{a}](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.expr.lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-02-12
# updated on 2019-02-12
