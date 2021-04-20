from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given):
    x = axiom.is_nonzero(given)
    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)

    Eq << apply(Unequal(a, 0))
    
    Eq << Eq[1].this.lhs.definition
    
    Eq << algebra.cond.given.ou.apply(Eq[-1])
    
    

if __name__ == '__main__':
    prove()
