from sympy import *
from axiom.utility import prove, apply


@apply
def apply(given):
    assert given.is_boolean
    return Equality(Boole(given), 1)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(GreaterThan(f(x), y))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    

if __name__ == '__main__':
    prove(__file__)

