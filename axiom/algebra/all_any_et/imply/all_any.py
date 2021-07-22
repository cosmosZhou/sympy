from util import *


@apply
def apply(given, index):
    (fn, *limits_e), *limits_f = given.of(All[Any])
    eqs, *limits = fn.of(All[And])

    return All(Any(All(eqs[index], *limits), *limits_e), *limits_f)


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
    Eq << apply(All[x:0:a](Any[y:0:b](All[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))), index=0)

    Eq << Eq[0].this.find(All).apply(algebra.all_et.imply.et.all)

    Eq << Eq[-1].this.expr.apply(algebra.any_et.imply.et.any)

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()

