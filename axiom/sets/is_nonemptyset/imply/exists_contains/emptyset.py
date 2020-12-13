from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Exists
from sympy import Symbol
from axiom import sets
# given: A != {}
# Exists[x] (x in A)


@plausible
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B
    x = A.element_symbol()
    return Exists[x](Contains(x, A))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    Eq << apply(Unequality(A, A.etype.emptySet))
    
    Eq <<= sets.imply.ou.contains.apply(Eq[0].lhs) & Eq[0]
    
    Eq << Eq[-1].split()

if __name__ == '__main__':
    prove(__file__)

