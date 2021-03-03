from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    contains, *limits = axiom.is_Exists(given)
    x, A = axiom.is_Contains(contains)
    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):    
    A = Symbol.A(etype=dtype.real, given=True)
    e = Symbol.e(real=True)

    Eq << apply(Exists[e](Contains(e, A)))
    
    Eq << sets.is_nonemptyset.imply.exists_contains.voidlimit.apply(Eq[1])


if __name__ == '__main__':
    prove(__file__)

