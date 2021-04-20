from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, divisor=None):
    lhs, rhs = axiom.is_Equal(given)    
    return Equal(lhs / divisor, rhs / divisor)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    d = Symbol.d(real=True, zero=False)
    
    Eq << apply(Equal(x, y), d)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove()

