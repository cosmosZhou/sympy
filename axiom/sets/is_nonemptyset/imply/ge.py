from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra

# given: A != {}
# |A| >= 1


@apply
def apply(given):
    assert given.is_Unequal
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B

    return GreaterEqual(abs(A), 1)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.is_positive.apply(Eq[0])
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].this.function.solve(Eq[-1].lhs)
    
    Eq << algebra.exists_eq.cond.imply.exists.subs.apply(Eq[-1], Eq[2])

    
if __name__ == '__main__':
    prove()

