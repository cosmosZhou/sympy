from sympy.core.relational import Equal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.sets.contains import NotContains
from axiom import sets, algebra
import axiom


# given A & B = {} => A - B = A
@apply
def apply(given):
    A = axiom.is_emptyset(given)
    return Equal(abs(A), 0)


@prove
def prove(Eq):
    
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(A, A.etype.emptySet))
    
    Eq << algebra.eq.imply.eq.abs.apply(Eq[0])
    

if __name__ == '__main__':
    prove()

