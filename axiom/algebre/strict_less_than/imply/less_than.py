from axiom.utility import plausible
from sympy.core.relational import LessThan
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.sets.contains import Contains
from axiom import sets


@plausible
def apply(given):
    assert given.is_StrictLessThan
    lhs, rhs = given.args
    assert lhs.is_integer and rhs.is_integer
    return LessThan(lhs, rhs - 1)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    Eq << apply(x < y)   
    
    Eq << Contains(x, Interval(-oo, y, right_open=True, integer=True), plausible=True) 
    
    Eq << Eq[-1].split()
    
    Eq << sets.contains.imply.contains.interval.apply(Eq[-1], 1, simplify=False)
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-1] - 1
    

if __name__ == '__main__':
    prove(__file__)
