from util import *


@apply
def apply(given):
    f, limit = given.of(Exists)
    x, S = limit
    return Unequal(S, x.emptySet)


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Exists[e:S](f(e) > 0))

    Eq << Exists[e:S](Contains(e, S) & Eq[0].function, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1])


if __name__ == '__main__':
    run()

