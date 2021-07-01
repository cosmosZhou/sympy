from util import *


@apply
def apply(given, index=-1):
    eqs, *limits = given.of(All[And])
    first = And(*eqs[:index])
    second = And(*eqs[index:])
    return All(first, *limits), All(second, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    f = Function.f(shape=(), real=True)
    Eq << apply(All[x:a:b]((x <= c) & (f(x) >= d)))

    Eq << algebra.all_et.imply.all.apply(Eq[0], 0)
    Eq << algebra.all_et.imply.all.apply(Eq[0], 1)




if __name__ == '__main__':
    run()