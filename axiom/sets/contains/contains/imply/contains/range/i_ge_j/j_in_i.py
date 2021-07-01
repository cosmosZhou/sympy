from util import *


@apply
def apply(contains_j, contains_i):
    j, Sj = contains_j.of(Contains)
    i, Si = contains_i.of(Contains)

    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)

    a_d, n = Si.of(Range)
    a, i_d = Sj.of(Range)

    d = i - i_d + 1
    assert a_d == a + d

    return Contains(i, Range(d + j, n)), Contains(j, Range(a, n - d))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(j, Range(a, i - d + 1)), Contains(i, Range(a + d, n)))

    Eq <<= sets.contains.given.et.split.range.apply(Eq[-2]), sets.contains.given.et.split.range.apply(Eq[-1])

    Eq <<= sets.contains.imply.et.split.range.apply(Eq[0]), sets.contains.imply.et.split.range.apply(Eq[1])

    Eq << Eq[-2] + d

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[5]) - d

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

