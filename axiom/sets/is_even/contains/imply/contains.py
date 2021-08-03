from util import *


@apply
def apply(*given):
    is_even, contains_n = given
    n = is_even.of(Equal[Expr % 2, 0])
    n_, ab = contains_n.of(Contains)

    assert n == n_
    a, b = ab.of(Range)
    b -= 1

    return Contains(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)
    Eq << apply(Equal(n % 2, 0), Contains(n, Range(a, b + 1)))

    Eq << algebra.is_even.imply.any.apply(Eq[0])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.subs)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.div.range, 2, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.imply.eq.div, 2, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.imply.eq.reverse, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.ceiling.to.floor)

    S = Symbol.S(conditionset(n, Eq[-1]))
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n)

    Eq << Contains(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()

