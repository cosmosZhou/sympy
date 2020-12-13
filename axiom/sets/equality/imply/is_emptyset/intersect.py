from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
# given : A \ B = A

# => A & B = EmptySet


@plausible
def apply(given):
    assert given.is_Equality
    assert given.lhs.is_Complement
    A, B = given.lhs.args
    assert given.rhs == A

    return Equality(A & B, A.etype.emptySet)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    
    Eq << apply(Equality(A - B, A))

    Eq << Eq[0].intersect(B).reversed
    
if __name__ == '__main__':
    prove(__file__)

