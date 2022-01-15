from util import *


@apply
def apply(any_all_0, any_all_1):
    from axiom.algebra.all.any.imply.any_all_et import limits_dependent
    (fn0, *limits_f0), *limits_e0 = any_all_0.of(Any[All])
    (fn1, *limits_f1), *limits_e1 = any_all_1.of(Any[All])

    assert not limits_dependent(limits_e0, limits_e1)
    assert not limits_dependent(limits_f0, limits_f1)

    return Any(All(fn0 & fn1, *limits_f0, *limits_f1), *limits_e0, *limits_e1)


@prove
def prove(Eq):
    from axiom import algebra

    N, M = Symbol(integer=True)
    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(Any[M](All[x:A](f(x) <= M)), Any[N](All[y:B](g(y) <= N)))

    Eq << Eq[-1].this.expr.apply(algebra.all_et.given.et.all)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.ou.given.cond.apply(Eq[-2], 1)

    Eq << algebra.ou.given.cond.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()

from . import limits_intersect
# created on 2019-02-24
