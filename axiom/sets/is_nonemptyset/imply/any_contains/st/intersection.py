from util import *



# given A & B != Ø
# then Any[e:B] e in A
@apply
def apply(given, wrt=None, domain=None):
    assert given.is_Unequal
    AB, emptyset = given.args
    if emptyset:
        tmp = AB
        AB = emptyset
        emptyset = tmp
    assert AB.is_Intersection
    A, B = AB.args
    if domain is None:
        domain = B
    else:
        if domain == A:
            A, B = B, A

    assert domain == B
    if wrt is None:
        wrt = B.element_symbol(A.free_symbols)
    assert wrt.type == B.etype
    return Any[wrt:B](Contains(wrt, A))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A & B, A.etype.emptySet))

    Eq << sets.imply.ou.contains.apply(A & B)

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.split.intersection, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=1, simplify=None)



if __name__ == '__main__':
    run()

