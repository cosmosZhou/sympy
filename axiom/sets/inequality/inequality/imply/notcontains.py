from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.sets.contains import NotContains
from sympy import Symbol
import axiom
from axiom import sets
# given: x != y
# x not in {y}


@plausible
def apply(*given):
    inequality_a, inequality_b = given
    x, a = axiom.is_Unequal(inequality_a)
    _x, b = axiom.is_Unequal(inequality_b)
    
    if x != _x:
        if x != b:
            x, a = a, x          
    
    assert x == _x
    return NotContains(x, {a, b})


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Unequality(x, a), Unequality(x, b))
    
    Eq << sets.inequality.imply.notcontains.apply(Eq[0], simplify=False)
    Eq << sets.inequality.imply.notcontains.apply(Eq[1], simplify=False)

    Eq << sets.notcontains.notcontains.imply.notcontains.union.apply(Eq[-1], Eq[-2], simplify=False)

    
if __name__ == '__main__':
    prove(__file__)

