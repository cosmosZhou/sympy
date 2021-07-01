from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Contains)
    j, Sj = contains_j.of(Contains)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    d_j, n = Si.of(Range)
    a, n_d = Sj.of(Range)

    d = n - n_d
    assert d_j == j + d

    return Contains(i, Range(a + d, n)), Contains(j, Range(a, i - d + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(i, Range(d + j, n)), Contains(j, Range(a, n - d)))

    Eq <<= sets.contains.given.et.split.range.apply(Eq[-2]), sets.contains.given.et.split.range.apply(Eq[-1])

    Eq <<= sets.contains.imply.et.split.range.apply(Eq[0]), sets.contains.imply.et.split.range.apply(Eq[1])

    Eq << Eq[-2] - d

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-1], Eq[6]) + d

    Eq << Eq[-1].reversed

    Eq << algebra.lt.given.le.apply(Eq[7])


if __name__ == '__main__':
    run()

