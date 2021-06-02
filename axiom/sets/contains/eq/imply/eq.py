
from util import *


import axiom


# given: A in B and |A| = |B|
# A = B
@apply
def apply(*given):
    contains, equal = given
    if contains.is_Equal and given[1].is_Contains:
        contains, equal = equal, contains

    a, A = contains.of(Contains)

    complement_A_a, complement_B_a = equal.of(Equal)
    _A, _a = complement_A_a.of(Complement)
    _a = _a.of(FiniteSet)

    assert a == _a
    B, _a = complement_B_a.of(Complement)
    _a = _a.of(FiniteSet)

    assert a == _a

    if A != _A:
        _A, B = B, _A
    assert A == _A

    return Equal(A, B | a.set)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(Contains(a, A), Equal(A // a.set, B // a.set))

    Eq << sets.eq.imply.eq.union.apply(Eq[1], a.set)

    Eq << sets.contains.imply.eq.union.apply(Eq[0])

    Eq << Eq[-2].this.lhs.subs(Eq[-1])

if __name__ == '__main__':
    run()

