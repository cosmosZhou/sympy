from axiom.utility import prove, apply
from sympy import *


@apply
def apply(given):
    assert given.is_ForAll
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](Contains(f(x), s)))
    
    Eq << Eq[-1].this.lhs.definition
    

if __name__ == '__main__':
    prove()

