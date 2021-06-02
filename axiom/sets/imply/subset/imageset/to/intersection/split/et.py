from util import *

import axiom


@apply
def apply(self):
    x, expr, et = axiom.is_ImageSet(self)
    eqs = et.of(And)
    return Subset(self, Intersection(*(imageset(x, expr, eq) for eq in eqs)))


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)

    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))

    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)

    Eq << apply(imageset(x, f(x), (g(x) > 0) & (h(x) > 0)))

    A = Symbol.A(conditionset(x, g(x) > 0))
    B = Symbol.B(conditionset(x, h(x) > 0))
    Eq << imageset(x, f(x), A & B).this.subs(A.this.definition)

    Eq << Eq[-1].this.rhs.limits[0][2].definition

    Eq << imageset(x, f(x), A).this.subs(A.this.definition)

    Eq << imageset(x, f(x), B).this.subs(B.this.definition)

    Eq << sets.imply.subset.imageset.to.intersection.split.intersection.apply(imageset(x, f(x), A & B))

    Eq << Eq[-1].subs(Eq[-2], Eq[-3], Eq[-4])


if __name__ == '__main__':
    run()

