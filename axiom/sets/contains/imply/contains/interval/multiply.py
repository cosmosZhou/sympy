from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply(imply=True)
def apply(given, d):
    assert given.is_Contains 
    d = sympify(d)   
    assert d.is_positive
    
    e, interval = given.args    
    
    assert interval.is_Interval
    a, b = interval.args
    
    e *= d
    
    return Contains(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    d = Symbol.d(real=True, positive=True)

    Eq << apply(Contains(x, Interval(a, b, right_open=True)), d)
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0]).split()
    
    Eq <<= Eq[-1] * d, Eq[-2] * d
    
    Eq << sets.greater_than.strict_less_than.imply.contains.apply(Eq[-2], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

