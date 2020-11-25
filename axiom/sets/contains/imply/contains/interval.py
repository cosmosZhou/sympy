from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.sets.sets import Interval


@plausible
def apply(given, t):
    assert given.is_Contains    
    
    e, interval = given.args    
    
    a, b, _ = interval.args
        
    return Contains(e + t, interval.copy(start=a + t, stop=b + t), given=given)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)
    
    Eq << apply(Contains(x, Interval(a, b)), t)
    Eq << Eq[0].split()
    
    Eq <<= Eq[-1] + t, Eq[-2] + t
    
    Eq <<= Eq[-1] & Eq[-2]

    
if __name__ == '__main__':
    prove(__file__)

