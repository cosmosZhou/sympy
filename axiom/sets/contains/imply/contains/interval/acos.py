from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains    
    
    e, interval = given.args    
    
    a, b = interval.args
    
    assert not interval.is_integer
        
    return Contains(acos(e), interval.func(acos(b), acos(a), left_open=interval.right_open, right_open=interval.left_open))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(Contains(x, Interval(a, b)))
    
    
if __name__ == '__main__':
    prove()

