from util import *


@apply
def apply(given, index=-1):
    (fn, *limits_e), *limits_f = given.of(All[Any])
    eqs, *limits = fn.of(All[And])

    first = And(*eqs[:index])
    second = And(*eqs[index:])


    return All(Any(All(first, *limits), *limits_e), *limits_f), All(Any(All(second, *limits), *limits_e), *limits_f)




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
    Eq << apply(All[x:0:a](Any[y:0:b](All[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))))

    Eq << algebra.all_any_et.imply.all_any.apply(Eq[0], index=0)
    Eq << algebra.all_any_et.imply.all_any.apply(Eq[0], index=1)






if __name__ == '__main__':
    run()