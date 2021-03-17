from axiom.utility import prove, apply
from sympy.core.relational import Equal, Unequal
from sympy import Symbol
import axiom
from sympy.logic.boolalg import Or
from axiom import algebre


@apply
def apply(given, y):
    x = axiom.is_zero(given)
    assert y.is_nonzero
    
    return Unequal(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    y = Symbol.y(real=True, zero=False)
    Eq << apply(Equal(a * b, 0), y)
    
    Eq << Eq[1].subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)
