from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra
import axiom


# given e not in S
@apply
def apply(imply):
    e, S = axiom.is_NotContains(imply)
    A, B = axiom.is_Union(S)
    return NotContains(e, A), NotContains(e, B)


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, B | A))

    Eq << sets.notcontains.notcontains.imply.notcontains.union.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    prove()

