from util import *


@apply
def apply(any_all_0, any_all_1):
    from sympy.concrete.limits import limits_dependent, limits_intersect
    (fn0, *limits_f0), *limits_e0 = any_all_0.of(Any[All])
    (fn1, *limits_f1), *limits_e1 = any_all_1.of(Any[All])

    assert not limits_dependent(limits_e0, limits_e1)

    assert len(limits_f0) == len(limits_f1)
    assert all(x == y for (x, *_), (y, *_) in zip(limits_f0, limits_f1))

    limits_f = limits_intersect(limits_f0, limits_f1)
    return Any(All(fn0 & fn1, *limits_f), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    from axiom import algebra
    N = Symbol.N(integer=True)
    M = Symbol.M(integer=True)

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Any[M](All[x:A](f(x) <= M)), Any[N](All[x:B](g(x) <= N)))

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.et)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[-2].this.function.apply(algebra.all.given.all.limits.relaxed, domain=A)

    Eq << Eq[-1].this.function.apply(algebra.all.given.all.limits.relaxed, domain=B)


if __name__ == '__main__':
    run()
