from axiom.utility import prove, apply
from sympy import *
from axiom import sets
import axiom


# given e not in S
@apply
def apply(given):
    e, S = axiom.is_NotContains(given)
    assert S.is_Interval
    
    if S.left_open:
        lower_bound = e <= S.start
    else:
        lower_bound = e < S.start
    if S.right_open:
        upper_bound = e >= S.stop
    else:
        upper_bound = e > S.stop
    
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    e = Symbol.e(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(NotContains(e, Interval(a, b)))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].apply(sets.le.ge.imply.contains)
    
    Eq << ~Eq[-1]

if __name__ == '__main__':
    prove()

