from util import *


@apply
def apply(*given):
    for cond in given:
        if cond.is_Equal:
            eq_sum = cond
        elif cond.is_GreaterEqual:
            ge = cond
        elif cond.is_All:
            all_is_nonnegative = cond
        else:
            return
        
    (xi, (i, _0, n)), a = eq_sum.of(Equal[Sum])
    xn, _a = ge.of(GreaterEqual)
    assert a == _a
    assert _0 == 0

    assert n > 0
    assert xn == xi._subs(i, n - 1)
    _xi, (_i, _0, _n) = all_is_nonnegative.of(All[Expr >= 0])
    assert _0 == 0
    assert n == _n
    assert _xi == xi and _i == i

    return Equal(xn, a), All[i:n - 1](Equal(xi, 0))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, shape=(oo,), given=True)
    n = Symbol.n(integer=True, given=True, negative=False)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True)
    Eq << apply(Equal(Sum[i:n + 1](x[i]), a), x[n] >= a, All[i:n + 1](x[i] >= 0))

    Eq.eq = Eq[0].this.lhs.apply(algebra.sum.to.add.pop_back)

    Eq.all_is_nonnegative = algebra.all.imply.all.limits.restrict.apply(Eq[2], domain=Range(0, n))

    Eq << algebra.all_is_nonnegative.imply.sum_is_nonnegative.apply(Eq.all_is_nonnegative)

    Eq << algebra.eq.ge.imply.le.sub.apply(Eq.eq, Eq[-1])

    Eq << algebra.ge.le.imply.eq.apply(Eq[1], Eq[-1])

    Eq << Eq.eq.subs(Eq[3])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    j = Symbol.j(integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(i, j)

    Eq << ~Eq[4]

    Eq << algebra.all.any.imply.any_et.apply(Eq.all_is_nonnegative, Eq[-1])

    Eq << Eq[-3].this.lhs.apply(algebra.sum.to.add.split, cond={i})

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().expr.find(Piecewise, Contains).simplify()

    Eq.any_is_negative = Eq[-1].this.expr.apply(algebra.eq.gt.imply.lt.sub)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq.all_is_nonnegative, Range(0, n) - {i})

    Eq << Eq[-1].limits_subs(i, j)

    Eq << algebra.all_is_nonnegative.imply.sum_is_nonnegative.apply(Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.any_is_negative)


if __name__ == '__main__':
    run()