from sympy.core.relational import LessThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Subset
from sympy import Symbol
from axiom import sets

# given: A ⊂ B
# |A| <= |B|
@plausible
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return LessThan(abs(A), abs(B), given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B))

    Eq << sets.subset.imply.equality.complement.apply(Eq[0])
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1] + Eq[-2].reversed

if __name__ == '__main__':
    prove(__file__)

