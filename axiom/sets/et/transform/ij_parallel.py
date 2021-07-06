from util import *


@apply(given=None)
def apply(given):
    contains_i, contains_j = given.of(And)
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
    
    return Equivalent(given, And(Contains(i, Range(_a + a, _b + b - 1)), Contains(j, Range(Max(a, i - _b + 1), Min(b, i - _a + 1)))))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(i, Range(d + j, n + j)) & Contains(j, Range(a, m)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.contains.contains.imply.contains.range.ij_parallel)

    Eq << Eq[-1].this.lhs.apply(sets.contains.contains.given.contains.range.ij_parallel)


if __name__ == '__main__':
    run()