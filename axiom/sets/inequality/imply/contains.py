from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.sets.contains import NotContains, Contains
from sympy import Symbol
# given: x != y
# x not in {y}


@plausible
def apply(given):
    assert given.is_Unequality
    x, y = given.args
    return Contains(x, y.universalSet - y.set)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequality(x, y))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].simplify()
    Eq << Eq[-1].subs(Eq[0])    
    

if __name__ == '__main__':
    prove(__file__)

