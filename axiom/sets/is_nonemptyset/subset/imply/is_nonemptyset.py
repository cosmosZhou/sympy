from util import *


@apply
def apply(*given, evaluate=False):
    assert len(given) == 2
    A = None
    B = None
    for p in given:
        if p.is_Subset:
            A, B = p.args
        elif p.is_Unequal:
            _A, _B = p.args
        else:
            return

    assert A == _A and B == _B or A == _B and B == _A
    return Unequal(B - A, A.etype.emptySet, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Unequal(A, B), Subset(A, B, evaluate=False))

    Eq << ~Eq[-1]

    Eq << sets.eq.imply.eq.union.apply(Eq[-1], A)

    Eq << Subset(B, A | B, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq <<= Eq[-1] & Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

