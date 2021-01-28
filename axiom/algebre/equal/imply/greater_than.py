from axiom.utility import prove, apply
from sympy.core.relational import Equality, GreaterThan
from sympy import Symbol


@apply(imply=True)
def apply(given):    
    assert given.is_Equality
    return GreaterThan(*given.args)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Equality(a, b))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove(__file__)
