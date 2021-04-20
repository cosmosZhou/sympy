from sympy import *
from axiom.utility import prove, apply
from axiom import sets
# given: A >= 1
# Exists[x] (x in A)


@apply
def apply(given):
    assert given.is_Greater
    abs_S, size = given.args
    assert size.is_extended_nonnegative
    assert abs_S.is_Abs
    S = abs_S.arg
    x = S.element_symbol()
    return Exists[x](Contains(x, S))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    Eq << apply(abs(A) > 0)
    
    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[0])
    
    Eq << sets.is_nonemptyset.imply.exists_contains.apply(Eq[-1], simplify=False)
    

if __name__ == '__main__':
    prove()

