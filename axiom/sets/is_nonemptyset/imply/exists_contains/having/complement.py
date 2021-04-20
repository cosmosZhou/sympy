from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


# given A & B != Ø
# then Exists[e:B] e in A
@apply
def apply(given, wrt=None, domain=None):
    AB = axiom.is_nonemptyset(given)
    
    A, B = axiom.is_Complement(AB)
    if wrt is None:
        wrt = A.element_symbol(B.free_symbols)
    assert wrt.type == B.etype
    return Exists[wrt:A](Contains(wrt, AB))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A // B, A.etype.emptySet))
    
    Eq << sets.is_nonemptyset.imply.exists_contains.apply(Eq[0])
    
    i = Eq[-1].variable
    
    Eq << Sufficient(Contains(i, A // B), And(Contains(i, A // B), Contains(i, A)), plausible=True)
    
    Eq << algebra.sufficient.given.sufficient.st.et.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.st.complement)
    
    Eq << Eq[2].this.function.apply(algebra.cond.sufficient.imply.cond.transit, Eq[-2], simplify=None)
    
    Eq << Eq[-1].apply(algebra.exists_et.imply.exists.limits_absorb, index=0, simplify=None)

if __name__ == '__main__':
    prove()

