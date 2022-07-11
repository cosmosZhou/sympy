from util import *


@apply
def apply(contains_i, contains_j):
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

    return Element(i, Range(a + d, n_d - 1 + d)), Element(j, Range(i - d + 1, n_d))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(a + d, j + d)), Element(j, Range(a + 1, n)))

    Eq << sets.el.imply.el.sub.apply(Eq[0], d)

    Eq << sets.el.given.el.sub.apply(Eq[2], d)

    Eq <<= sets.el_range.given.et.apply(Eq[3]), sets.el_range.given.et.apply(Eq[-1])

    Eq <<= sets.el_range.imply.et.apply(Eq[4]), sets.el_range.imply.et.apply(Eq[1])

    Eq << Eq[-2].reversed

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[7])

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-4], Eq[-1])

    Eq << algebra.ge.given.gt.apply(Eq[6])


if __name__ == '__main__':
    run()

from . import left_close
# created on 2021-01-29
