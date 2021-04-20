from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(sub):
    y, x = axiom.is_Substract(sub)
    
    if y == ceiling(x):
        return Equal(sub, frac(-x))
    if x == floor(y):
        return Equal(sub, frac(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x) - x)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)

    
if __name__ == '__main__':
    prove()
