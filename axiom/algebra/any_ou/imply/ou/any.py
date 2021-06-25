from util import *


@apply
def apply(imply):
    eqs, *limits = imply.of(Any[Or])

    return Or(*(Any(eq, *limits) for eq in eqs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real, given=True)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.all.all.imply.all_et.limits_intersect)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

