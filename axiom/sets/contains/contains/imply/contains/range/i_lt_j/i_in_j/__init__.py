from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Contains)
    j, Sj = contains_j.of(Contains)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    a_d, d_j = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = d_j - j
    a -= 1
    assert d == a_d - a

    return Contains(i, Range(a + d, n_d - 1 + d)), Contains(j, Range(i - d + 1, n_d))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(i, Range(a + d, j + d)), Contains(j, Range(a + 1, n)))

    Eq << sets.contains.imply.contains.sub.apply(Eq[0], d)

    Eq << sets.contains.given.contains.sub.apply(Eq[2], d)

    Eq <<= sets.contains.given.et.split.range.apply(Eq[3]), sets.contains.given.et.split.range.apply(Eq[-1])

    Eq <<= sets.contains.imply.et.split.range.apply(Eq[4]), sets.contains.imply.et.split.range.apply(Eq[1])

    Eq << Eq[-2].reversed

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[7])

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-4], Eq[-1])

    Eq << algebra.ge.given.gt.apply(Eq[6])


if __name__ == '__main__':
    run()

from . import left_close
