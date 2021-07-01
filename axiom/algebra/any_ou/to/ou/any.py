from util import *


@apply(given=None)
def apply(imply):
    ou, *limits = imply.of(Any[Or])

    return Equivalent(imply, Or(*(Any(eq, *limits) for eq in ou)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any_ou.imply.ou.any)

    Eq << Eq[-1].this.lhs.apply(algebra.any_ou.given.ou.any)


if __name__ == '__main__':
    run()

