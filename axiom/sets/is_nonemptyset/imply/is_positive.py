from sympy.core.relational import Unequal, Greater, GreaterEqual
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import S
from sympy import Symbol
from sympy.sets.sets import EmptySet
from axiom import sets, algebra
# given: A != {}
# |A| > 0


@apply
def apply(given):
    assert given.is_Unequal
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B

    return Greater(abs(A), 0)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    inequality = Unequal(A, EmptySet(), evaluate=False)

    Eq << apply(inequality)

    Eq << sets.is_nonemptyset.imply.is_nonzero.apply(Eq[0])
    
    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    prove()

