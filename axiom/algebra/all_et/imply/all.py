from util import *


@apply
def apply(given, index=None):
    eqs, *limits = given.of(ForAll[And])
    if index is None:
        return tuple(ForAll(eq, *limits)for eq in eqs)
    eq = eqs[index]
    return ForAll(eq, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True)
    f = Function.f(shape=(), real=True)

    Eq << apply(ForAll[x:a:b]((x <= c) & (f(x) >= 1)), index=0)

    Eq << ~Eq[-1]

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

