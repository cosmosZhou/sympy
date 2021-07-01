from util import *


@apply
def apply(*given):
    from sympy.concrete.limits import limits_dependent
    any_all_0, any_all_1 = given
    (fn0, *limits_f0), *limits_e0 = any_all_0.of(Any[All])
    (fn1, *limits_f1), *limits_e1 = any_all_1.of(Any[All])

    assert not limits_dependent(limits_e0, limits_e1)
    assert not limits_dependent(limits_f0, limits_f1)

    return Any(All(fn0 & fn1, *limits_f0, *limits_f1), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    from axiom import algebra
    N = Symbol.N(integer=True)
    M = Symbol.M(integer=True)

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Any[M](All[x:A](f(x) <= M)), Any[N](All[y:B](g(y) <= N)))

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.et.all)

    Eq << algebra.et.given.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

from . import limits_intersect
