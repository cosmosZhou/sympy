from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum, identity
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.concrete.expr_with_limits import Exists

from sympy import Piecewise


@plausible
def apply(a, b):    
    return Equality(a.set & b.set, Piecewise((a.set, Equality(a, b)), (S.EmptySet, True)).simplify())


from sympy.utility import check


@check
def prove(Eq):
    a = Symbol('a', integer=True)
    b = Symbol('b', integer=True)

    Eq << apply(a, b)
    
    A = Symbol('A', dtype=dtype.integer, definition=Eq[0].lhs)
    B = Symbol('B', dtype=dtype.integer, definition=Eq[0].rhs)
    Eq << Equality.by_definition_of(A)
    Eq << Equality.by_definition_of(B)

    Eq << identity(A & B).subs(Eq[-2])
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])

if __name__ == '__main__':
    prove(__file__)

