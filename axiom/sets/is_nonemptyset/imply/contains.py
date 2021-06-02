from util import *



@apply
def apply(given):
    assert given.is_Unequal
    A, emptyset = given.args
    assert A.is_Intersection and emptyset.is_EmptySet

    e_set, s = A.args
    if not e_set.is_FiniteSet:
        s, e_set = A.args
        assert e_set.is_FiniteSet

    assert len(e_set) == 1

    e, *_ = e_set.args

    return Contains(e, s)




@prove
def prove(Eq):
    from axiom import sets
    s = Symbol.s(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(Unequal(e.set & s, e.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(sets.notcontains.imply.is_emptyset.intersection)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

