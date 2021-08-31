from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.all.to.et.doit.setlimit import doit
    return Equivalent(self, doit(Any, self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo, k))
    i, j, a, b, c, d = Symbol(integer=True)
    f = Function(integer=True)


    Eq << apply(Any[i:{a, b, c, d}](x[i] > 0))

    Eq << Equivalent(Any[i:{a}](x[i] > 0), x[a] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equivalent(Any[i:{b}](x[i] > 0), x[b] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(Any[i:{c}](x[i] > 0), x[c] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(Any[i:{d}](x[i] > 0), x[d] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.equivalent.equivalent.imply.equivalent.ou.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

