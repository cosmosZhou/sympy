from axiom.utility import prove, apply
from sympy import *


@apply
def apply(given):
    return Equal(Bool(given.invert()), 0)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))
    
    Eq << Eq[-1].this.lhs.definition
    

if __name__ == '__main__':
    prove()

