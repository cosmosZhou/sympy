from util import *


@apply
def apply(contains_j, contains_i):
    j, Sj = contains_j.of(Element)
    i, Si = contains_i.of(Element)

    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)

    a_d, n_d = Si.of(Range)
    i_d, n = Sj.of(Range)

    d = i - i_d

    a = a_d - d
    assert n_d == n + d

    return Element(i, Range(a + d, d + j + 1)), Element(j, Range(a, n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(j, Range(i - d + 1, n)), Element(i, Range(a + d, d + n - 1)))

    Eq << sets.el.imply.el.sub.apply(Eq[1], d)

    Eq << sets.el.given.el.sub.apply(Eq[2], d)

    Eq <<= sets.el_range.given.et.apply(Eq[-1]), sets.el_range.given.et.apply(Eq[3])

    Eq <<= sets.el_range.imply.et.apply(Eq[0]), sets.el_range.imply.et.apply(Eq[4])

    Eq << algebra.ge.imply.gt.relax.apply(Eq[-2])

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[6])

    Eq << Eq[-2].reversed

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

from . import left_close
# created on 2021-01-29
