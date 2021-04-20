from sympy import *
from axiom.utility import prove, apply


@apply
def apply(given):
    assert given.is_boolean
    return Equal(Bool(given.invert()), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(GreaterEqual(f(x), y))
    
    Eq << Eq[-1].this.lhs.definition
    

if __name__ == '__main__':
    prove()

