from sympy.core.relational import GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Supset
from sympy import Symbol
from axiom import sets

# given: A ⊃ B
# |A| >= |B|
@plausible
def apply(given):
    assert given.is_Supset
    A, B = given.args

    return GreaterThan(abs(A), abs(B))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Supset(A, B))
    
    Eq << Eq[0].reversed

    Eq << sets.subset.imply.less_than.apply(Eq[-1])
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove(__file__)

