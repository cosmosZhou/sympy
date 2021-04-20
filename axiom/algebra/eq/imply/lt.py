from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given, b):    
    x, y = axiom.is_Equal(given)
    assert y < b
    return Less(x, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Equal(a, b), b + 1)
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove()
