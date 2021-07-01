from util import *


@apply
def apply(*given):
    cond, exists = given
    (fn, *limits_e), *limits_f = exists.of(All[Any])
    return All(Any(cond & fn, *limits_e), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra

    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    B = Symbol.B(etype=dtype.real)
    A = Symbol.A(etype=dtype.real)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(f(x, y) > 0, All[y:B](Any[x:A]((g(x, y) > 0))))

    Eq << Eq[-1].this.function.apply(algebra.any_et.given.et, index=0)

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << algebra.all.given.cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

