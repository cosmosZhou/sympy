from util import *


@apply(given=None)
def apply(imply):
    ou, *limits = imply.of(Any[Or])

    return Equivalent(imply, Or(*(Any(eq, *limits) for eq in ou)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g = Function(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any_ou.imply.ou.any)

    Eq << Eq[-1].this.lhs.apply(algebra.any_ou.given.ou.any)


if __name__ == '__main__':
    run()

# created on 2019-02-28
