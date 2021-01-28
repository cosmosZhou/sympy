from axiom.utility import prove, apply
from sympy.core.relational import LessThan
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.sets.contains import Contains
from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_StrictLessThan
    lhs, rhs = given.args
    if lhs.is_integer and rhs.is_integer:
        return LessThan(lhs, rhs - 1)
    return LessThan(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    Eq << apply(x < y)   
    
    Eq << Contains(x, Interval(-oo, y, right_open=True, integer=True), plausible=True) 
    
    Eq << Eq[-1].split()
    
    Eq << sets.contains.imply.contains.interval.add.apply(Eq[-1], 1, simplify=False)
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-1] - 1
    

if __name__ == '__main__':
    prove(__file__)
