from util import *


@apply
def apply(*given):
    from sympy.concrete.limits import limits_union
    any_all, forall = given
    forall0, *limits_e = any_all.of(Exists)

    cond, *limits_f0 = forall0.of(ForAll)
    _cond, *limits_f1 = forall.of(ForAll)
    assert forall0.variables == forall.variables
    assert _cond == _cond

    limits_f = limits_union(limits_f0, limits_f1)
    return Exists(ForAll(cond, *limits_f), *limits_e)


@prove
def prove(Eq):
    from axiom import algebra
    N = Symbol.N(integer=True)
    g = Function.g(shape=(), integer=True)
    M = Symbol.M(g(N))
    n = Symbol.n(integer=True)
    f = Function.f(shape=(), integer=True)
    Eq << apply(Exists[N](ForAll[n:N:oo](f(n) <= M)), ForAll[n:N](f(n) <= M))

    Eq << Eq[1].this.function.apply(algebra.all.all.imply.all.limits_union, Eq[2])


if __name__ == '__main__':
    run()
