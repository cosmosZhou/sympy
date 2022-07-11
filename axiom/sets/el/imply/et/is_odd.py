from util import *


@apply
def apply(given):
    n, (__n, (_n, a, b)) = given.of(Element[Cup[FiniteSet[2 * Expr + 1], Tuple[Floor, Floor + 1]]])
    assert n == _n == __n

    a = 2 * a
    b = 2 * b + 1

    return Equal(n % 2, 1), Element(n, Range(a, b + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1))))

    S = Symbol(Eq[0].rhs)
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, (n - 1) / 2)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq.contains = Eq[-1].subs(Eq[-2]).simplify()

    Eq << sets.el.imply.el.mul.range.apply(Eq.contains, 2)

    Eq.greater_than, Eq.less_than = sets.el_range.imply.et.apply(Eq[-1], right_open=False)

    Eq.strict_greater_than = algebra.ge.imply.gt.relax.apply(Eq.greater_than)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq.strict_greater_than, algebra.imply.ge.floor.integer.apply(a, 2))

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << algebra.imply.le.floor.apply((b - 1) / 2) * 2 + 1

    Eq << algebra.le.le.imply.le.transit.apply(Eq.less_than, Eq[-1])

    Eq << sets.ge.le.imply.el.range.apply(Eq[-3], Eq[-1])

    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq.contains, Eq[-1])

    Eq << sets.el.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1] * 2 + 1

    Eq << Eq[-1] % 2


if __name__ == '__main__':
    run()

# created on 2018-05-30
