from axiom.utility import prove, apply

from sympy import *
from axiom import sets
# given0: A in B
# given1: B & C = {}
# C - A = C
@apply
def apply(*given):
    assert len(given) == 2
    A = None
    B = None
    for p in given:
        if p.is_Subset:
            A, B = p.args
        elif p.is_Equal:
            BC, emptyset = p.args
            if emptyset:
                tmp = emptyset
                emptyset = BC
                BC = tmp
            assert BC.is_Intersection
            _B, C = BC.args
        else:
            return

    if B != _B:
        assert B == C
        C = _B

    return Equal(C - A, C)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)

    Eq << apply(Equal(B & C, C.etype.emptySet, evaluate=False), Subset(A, B, evaluate=False))

    Eq << sets.is_emptyset.subset.imply.is_emptyset.apply(Eq[0], Eq[1])

    Eq << sets.eq.imply.eq.union.apply(Eq[-1], Eq[-2].lhs)
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

