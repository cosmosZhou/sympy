from util import *


@apply
def apply(given, index=None):
    eqs, *limits = given.of(All[Or])

    if index is None:
        return tuple(All(eq, *limits) for eq in eqs)

    return All(eqs[index], *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)

    f = Function.f(shape=(), real=True)

    Eq << apply(All[x:a:b]((x <= c) | (f(x) >= 1)), index=0)

    Eq << ~Eq[0]

    Eq << algebra.all.any.imply.any_et.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

