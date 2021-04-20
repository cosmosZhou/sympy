from sympy.core.relational import Equal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from axiom import sets
# given: |A| = 0
# A == {}


@apply
def apply(given):
    assert given.is_Equal
    A, B = given.args
    if B != 0:
        A = B
    assert A.is_Abs
    A = A.arg

    return Equal(A, A.etype.emptySet)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(abs(A), 0))

    Eq << ~Eq[-1]
    
    Eq << sets.is_nonemptyset.imply.is_nonzero.apply(Eq[-1])
    
    Eq << ~Eq[0]

if __name__ == '__main__':
    prove()

