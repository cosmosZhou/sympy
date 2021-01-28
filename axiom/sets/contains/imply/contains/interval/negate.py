from axiom.utility import prove, apply
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.sets.sets import Interval


@apply(imply=True)
def apply(given):
    assert given.is_Contains    
    
    e, interval = given.args    
    
    return Contains(-e, -interval)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))
    Eq << Eq[0].split()

    Eq <<= -Eq[-1], -Eq[-2]
    
    Eq << Eq[1].split()

    
if __name__ == '__main__':
    prove(__file__)

