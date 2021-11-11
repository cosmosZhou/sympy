from util import *


@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    _a, _b = Si.of(Range)
    _a -= j
    _b -= j

    assert not _a._has(j) and not _b._has(j)
    a, b = Sj.of(Range)

    return Equivalent(given, And(Element(i, Range(_a + a, _b + b - 1)), Element(j, Range(Max(a, i - _b + 1), Min(b, i - _a + 1)))))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, i, j, n, m, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(d + j, n + j)) & Element(j, Range(a, m)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el.el.imply.el.range.ij_parallel)

    Eq << Eq[-1].this.lhs.apply(sets.el.el.given.el.range.ij_parallel)


if __name__ == '__main__':
    run()
# created on 2020-03-21
# updated on 2020-03-21
