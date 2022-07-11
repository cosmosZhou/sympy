from util import *


@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    d_j, n = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = n - n_d
    assert d_j == j + d

    return Equivalent(given, And(Element(j, Range(a, i - d + 1)), Element(i, Range(a + d, n))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a, i, j, n, d = Symbol(integer=True)

    Eq << apply(Element(i, Range(d + j, n)) & Element(j, Range(a, n - d)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el.el.imply.el.range.i_ge_j.i_in_j)

    Eq << Eq[-1].this.rhs.apply(sets.el.el.imply.el.range.i_ge_j.j_in_i)


if __name__ == '__main__':
    run()

# created on 2019-11-06
