from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(S):
    assert S.is_set
    
    e = S.element_symbol()
    return Exists(Contains(e, S), (e,)) | Equality(S, e.emptySet)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)

    Eq << apply(S)
    
    Eq << Eq[-1].bisect(Unequal(S, S.etype.emptySet))
    
    Eq << Eq[-1].this.function.apply(sets.exists_contains.given.is_nonemptyset, depth=0)


if __name__ == '__main__':
    prove(__file__)

