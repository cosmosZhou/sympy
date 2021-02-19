from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
import axiom
from sympy.sets.sets import FiniteSet
# given : A & B = A | B => A = B


@apply
def apply(given):
    A, B = axiom.is_Equal(given)
    return Equality(FiniteSet(A), FiniteSet(B))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equality(A, B))
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    prove(__file__)

