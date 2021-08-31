from util import *


@apply
def apply(subset, equal):
    C, A = subset.of(Subset)

    complement_A_C, complement_B_C = equal.of(Equal)
    _A, _C = complement_A_C.of(Complement)
    assert C == _C
    B, _C = complement_B_C.of(Complement)
    assert C == _C

    if A != _A:
        _A, B = B, _A
    assert A == _A

    return Equal(A, B | C)


@prove
def prove(Eq):
    from axiom import sets
    A, B, C = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(C, A), Equal(A - C, B - C))

    Eq << sets.eq.imply.eq.union.apply(Eq[1], C)

    Eq << sets.subset.imply.eq.union.apply(Eq[0])

    Eq << Eq[-2].this.lhs.subs(Eq[-1])


if __name__ == '__main__':
    run()
