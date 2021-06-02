from util import *


@apply
def apply(*given):
    forall, all_any = given
    from sympy.concrete.limits import limits_include, limits_difference
    fx, *limits_a = forall.of(ForAll)

    exists, *limits_b = all_any.of(ForAll)
    assert limits_include(limits_a, limits_b)

    limits_a = limits_difference(limits_a, limits_b)

    assert limits_a
    fy, *limits_c = exists.of(Exists)
    return ForAll(Exists(ForAll(fx & fy, *limits_a), *limits_c), *limits_b)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(shape=(oo,), etype=dtype.integer)

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(domain=Range(0, k + 1))
    s = Symbol.s(etype=dtype.integer.set * (k + 1))

    Eq << apply(ForAll[i:Range(0, k + 1) // {j}, x[:k + 1]:s](Equal(x[i] & x[j], x[i].etype.emptySet)),
                ForAll[x[:k + 1]:s](Exists[j](Subset({n}, x[j]))))

    Eq << Eq[-1].this.function.function.apply(algebra.all.given.ou)

    Eq << Eq[-1].this.function.apply(algebra.any_ou.given.ou.any, simplify=None)

    Eq << Eq[-1].this.find(Exists).apply(algebra.any.given.cond, simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.ou.given.all)

    Eq << Eq[-1].this.function.apply(algebra.any_et.given.et, index=0)

    Eq << algebra.all_et.given.all.apply(Eq[-1])


if __name__ == '__main__':
    run()

