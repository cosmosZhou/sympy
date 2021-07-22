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

    Eq.ge, Eq.lt = sets.contains.imply.et.split.range.apply(Eq[0])

    Eq << Eq.ge.this.apply(algebra.ge.transposition, rhs=0)

    Eq << Eq.lt.this.apply(algebra.lt.transposition, rhs=-1)

    Eq << sets.lt.ge.imply.contains.range.apply(Eq[-1], Eq[-2])

    Eq <<= Eq[1] & Eq[-1]

    Eq << sets.contains.imply.et.split.range.apply(Eq[1])

    Eq <<= algebra.ge.ge.imply.ge.transit.apply(Eq.ge, Eq[-2] + d), algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq.lt, Eq[-1] + n)

    Eq << sets.lt.ge.imply.contains.range.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()