from sympy.core.relational import Unequality, GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype 
from axiom import sets
from sympy import Symbol
# given: A != {}
# |A| >= 1


@plausible
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B

    return GreaterThan(abs(A), 1)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    inequality = Unequality(A, A.etype.emptySet)

    Eq << apply(inequality)

    Eq << sets.is_nonemptyset.imply.is_positive.apply(inequality)
    
    Eq << ~Eq[1]
    Eq << Eq[-1].this.function.solve(Eq[-1].lhs)
    
    Eq << Eq[2].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

