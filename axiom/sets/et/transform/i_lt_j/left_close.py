from util import *


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
    i, Si = contains_i.of(Contains)
    j, Sj = contains_j.of(Contains)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    a_d, d_j = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = d_j - j

    assert d == a_d - a

    return Equivalent(given, And(Contains(i, Range(a + d, n_d + d)), Contains(j, Range(i - d + 1, n_d))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(And(Contains(i, Range(a + d, j + d)), Contains(j, Range(a, n))))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.contains.contains.imply.contains.range.i_lt_j.i_in_j.left_close)

    Eq << Eq[-1].this.rhs.apply(sets.contains.contains.imply.contains.range.i_lt_j.j_in_i.left_close)


if __name__ == '__main__':
    run()

