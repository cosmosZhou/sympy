from util import *


@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
    i, Si = contains_i.of(Contains)
    j, Sj = contains_j.of(Contains)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    d_j, n = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = n - n_d
    assert d_j == j + d

    return Equivalent(given, And(Contains(j, Range(a, i - d + 1)), Contains(i, Range(a + d, n))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Contains(i, Range(d + j, n)) & Contains(j, Range(a, n - d)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.contains.contains.imply.contains.range.i_ge_j.i_in_j)

    Eq << Eq[-1].this.rhs.apply(sets.contains.contains.imply.contains.range.i_ge_j.j_in_i)


if __name__ == '__main__':
    run()

