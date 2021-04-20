from axiom.utility import prove, apply
from sympy import *
from axiom import sets


# given0: A in B
# given1: B & C = {}
# and C & A = {}
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

    return Equal(C & A, A.etype.emptySet)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    Eq << apply(Equal(B & C, C.etype.emptySet, evaluate=False), Subset(A, B, evaluate=False))
    
    Eq << sets.subset.imply.subset.intersect.apply(Eq[1], C)
    
    Eq << Eq[-1].subs(Eq[0])

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove()

