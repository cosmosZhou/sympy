from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit
    return Equivalent(self, doit(Any, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    g = Function.g(etype=dtype.integer)

    a = Symbol.a(integer=True)

    Eq << apply(Any[i:g(i), j:f(i, j) > 0, i:{a}](x[i, j] > 0))

    Eq << Equivalent(Any[i:{a}](Equal(Bool(Any[i:g(i), j:f(i, j) > 0](x[i, j] > 0)), 1)),
                     Any[i:g(i), j:f(i, j) > 0, i:{a}](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.lhs.expr.lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

