from util import *


@apply
def apply(given, index=0):
    eqs, *limits = given.of(All[And])
    eq = eqs[index]
    return All(eq, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True, given=True)
    d = Symbol.d(real=True, given=True)
    f = Function.f(shape=(), real=True)
    Eq << apply(All[x:a:b]((x <= c) & (f(x) >= d)), index=0)

    Eq << ~Eq[-1]

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()


