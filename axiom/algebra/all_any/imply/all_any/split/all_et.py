from util import *


@apply
def apply(given, index=None):
    (fn, *limits_e), *limits_f = given.of(ForAll[Exists])
    eqs, *limits = fn.of(ForAll[And])

    if index is None:
        return tuple(ForAll(Exists(ForAll(eq, *limits), *limits_e), *limits_f) for eq in eqs)

    return ForAll(Exists(ForAll(eqs[index], *limits), *limits_e), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(ForAll[x:0:a](Exists[y:0:b](ForAll[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))), index=0)

    Eq << Eq[0].this.function.function.apply(algebra.all_et.imply.et)

    Eq << Eq[-1].this.function.apply(algebra.any_et.imply.et.split)

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()

