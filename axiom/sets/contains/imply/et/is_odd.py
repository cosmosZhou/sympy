from util import *


@apply
def apply(given):    
    n, (__n, (_n, a, b)) = given.of(Contains[Cup[FiniteSet[2 * Expr + 1], Tuple[Floor, Floor + 1]]])
    assert n == _n == __n

    a = 2 * a
    b = 2 * b + 1

    return And(Equal(n % 2, 1), Contains(n, Range(a, b + 1)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Contains(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1))))

    S = Symbol.S(Eq[0].rhs)
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, (n - 1) / 2)

    Eq << Contains(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq.contains = Eq[-1].subs(Eq[-2]).simplify()

    Eq << sets.contains.imply.contains.range.mul.apply(Eq.contains, 2)

    Eq << sets.contains.imply.et.split.range.apply(Eq[-1], right_open=False)

    Eq.less_than, Eq.greater_than = algebra.et.imply.conds.apply(Eq[-1])

    Eq.strict_greater_than = algebra.ge.imply.gt.transit.apply(Eq.greater_than)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq.strict_greater_than, algebra.imply.ge.floor.apply(a, 2))

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << algebra.imply.le.floor.apply(b - 1, 2) + 1

    Eq << algebra.le.le.imply.le.transit.apply(Eq.less_than, Eq[-1])

    Eq << sets.ge.le.imply.contains.range.apply(Eq[-3], Eq[-1])

    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq.contains, Eq[-1])

    Eq << sets.contains.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1] * 2 + 1

    Eq << Eq[-1] % 2

    Eq << algebra.et.given.conds.apply(Eq[1])


if __name__ == '__main__':
    run()

