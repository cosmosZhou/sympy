from axiom.utility import plausible
from sympy.core.relational import Unequal
from sympy import Symbol


@plausible
def apply(given):
    assert given.is_StrictGreaterThan
    
    return Unequal(*given.args, given=given)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(x > y)
    
    Eq << ~Eq[-1]
    Eq << Eq[0].subs(Eq[-1])
    
    

if __name__ == '__main__':
    prove(__file__)
