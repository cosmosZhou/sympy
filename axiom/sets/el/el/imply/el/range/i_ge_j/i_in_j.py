from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    d_j, n = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = n - n_d
    assert d_j == j + d

    return Element(i, Range(a + d, n)), Element(j, Range(a, i - d + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(d + j, n)), Element(j, Range(a, n - d)))

    Eq <<= sets.el_range.given.et.apply(Eq[-2]), sets.el_range.given.et.apply(Eq[-1])

    Eq <<= sets.el_range.imply.et.apply(Eq[0]), sets.el_range.imply.et.apply(Eq[1])

    Eq << Eq[-2] - d

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-1], Eq[6]) + d

    Eq << Eq[-1].reversed

    Eq << algebra.lt.given.le.apply(Eq[7])


if __name__ == '__main__':
    run()

# created on 2019-11-05
