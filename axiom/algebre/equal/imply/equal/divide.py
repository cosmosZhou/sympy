from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given, divisor=None):
    lhs, rhs = axiom.is_Equal(given)    
    return Equality(lhs / divisor, rhs / divisor)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    d = Symbol.d(real=True, zero=False)
    
    Eq << apply(Equality(x, y), d)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)

