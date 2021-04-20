from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(notcontains): 
    x, ab = axiom.is_NotContains(notcontains)

    assert ab.is_Interval
    assert ab.right_open

    b = ab.stop
    return Equal(x, b) | NotContains(x, ab.copy(right_open=False))            


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(NotContains(x, Interval(a, b, right_open=True)))
    
    Eq << sets.ou.imply.notcontains.interval.apply(Eq[1])
    
        
if __name__ == '__main__':
    prove()

