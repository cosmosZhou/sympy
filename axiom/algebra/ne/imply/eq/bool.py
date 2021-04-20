from axiom.utility import prove, apply
from sympy import *


@apply
def apply(given):
    assert given.is_Unequal
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Unequal(f(x), y))
    
    Eq << Eq[-1].this.lhs.definition
    

if __name__ == '__main__':
    prove()

