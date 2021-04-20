from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given):
    boole, one = axiom.is_Equal(given)
    if not one.is_One:
        boole, one = one, boole
    assert one.is_One
    
    cond = axiom.is_Bool(boole)
         
    return Equivalent(given, cond)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    Eq << apply(Equal(Bool(Contains(x, A)), 1))
    
    Eq << Eq[-1].this.lhs.lhs.definition
    
    
if __name__ == '__main__':
    prove()
