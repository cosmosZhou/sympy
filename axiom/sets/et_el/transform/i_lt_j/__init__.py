from util import *


@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    a_d, d_j = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = d_j - j
    a -= 1
    assert d == a_d - a

    return Equivalent(given, And(Element(i, Range(a + d, n_d - 1 + d)), Element(j, Range(i - d + 1, n_d))))


@prove
def prove(Eq):
    from axiom import sets, algebra
    a, i, j, n, d = Symbol(integer=True)

    Eq << apply(And(Element(i, Range(a + d, j + d)), Element(j, Range(a + 1, n))))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el.el.imply.el.range.i_lt_j.i_in_j)

    Eq << Eq[-1].this.rhs.apply(sets.el.el.imply.el.range.i_lt_j.j_in_i)


if __name__ == '__main__':
    run()

# created on 2021-01-30
from . import left_close
