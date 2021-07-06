from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Contains)
    j, Sj = contains_j.of(Contains)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    _a, _b = Si.of(Range)
    _a -= j
    _b -= j

    assert not _a._has(j) and not _b._has(j)
    a, b = Sj.of(Range)

    return Contains(i, Range(_a + a, _b + b - 1)), Contains(j, Range(Max(a, i - _b + 1), Min(b, i - _a + 1)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(i, Range(d + j, n + j)), Contains(j, Range(a, m)))

    Eq <<= sets.contains.given.et.split.range.apply(Eq[0]), sets.contains.given.et.split.range.apply(Eq[1]), sets.contains.imply.et.split.range.apply(Eq[-1])

    Eq <<= algebra.ge_max.imply.et.ge.apply(Eq[-2]), algebra.lt_min.imply.et.lt.apply(Eq[-1])

    Eq << algebra.le.imply.lt.relax.apply(Eq[-2].reversed + n, lower=i)

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1]).reversed + d


if __name__ == '__main__':
    run()