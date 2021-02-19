from axiom.utility import prove, apply
from sympy.core.relational import Unequal
from sympy import Symbol


@apply
def apply(given):
    assert given.is_StrictGreaterThan
    
    return Unequal(*given.args)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(x > y)
    
    Eq << ~Eq[-1]
    Eq << Eq[0].subs(Eq[-1])
    
    

if __name__ == '__main__':
    prove(__file__)
