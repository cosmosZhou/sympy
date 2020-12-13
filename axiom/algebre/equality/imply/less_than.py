from axiom.utility import plausible
from sympy.core.relational import Equality, LessThan
from sympy import Symbol


@plausible
def apply(given):    
    assert given.is_Equality
    return LessThan(*given.args)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Equality(a, b))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove(__file__)
