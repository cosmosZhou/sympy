from sympy import *
from axiom.utility import prove, apply
from axiom import sets


# given A & B != Ø
# then Exists[e:B] e in A
@apply
def apply(given, wrt=None, domain=None):
    assert given.is_Unequality
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
    return Exists[wrt:B](Contains(wrt, A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    inequality = Unequality(A & B, A.etype.emptySet)
    Eq << apply(inequality)

    Eq << sets.imply.ou.contains.apply(A & B)

    Eq << (Eq[-1] & inequality)

    Eq << Eq[-1].split()
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.where.intersection, simplify=None)
    
    Eq << Eq[-1].split(simplify=False)

    Eq << (~Eq[1]).limits_subs(Eq[1].variable, Eq[-1].variable)
    
    Eq << (Eq[-1] & Eq[-3])


if __name__ == '__main__':
    prove(__file__)

