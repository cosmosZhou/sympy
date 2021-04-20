from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, R = axiom.is_Contains(given)
    assert R.is_Interval
    assert R.start == -oo
    assert R.stop == 0
    assert x.is_complex
    return LessEqual(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Interval(-oo, 0)))
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]
    
        

if __name__ == '__main__':
    prove()

