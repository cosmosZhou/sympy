from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(S):
    assert S.is_set
    
    e = S.element_symbol()
    return Exists(Contains(e, S), (e,)) | Equal(S, e.emptySet)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq << Eq[-1].apply(algebra.cond.given.et.forall, cond=Unequal(S, S.etype.emptySet))
    
    Eq << Eq[-1].this.function.apply(sets.exists_contains.given.is_nonemptyset)


if __name__ == '__main__':
    prove()

