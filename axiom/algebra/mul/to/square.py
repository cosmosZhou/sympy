from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, evaluate=False):
    args = []
    
    for arg in axiom.is_Mul(self, copy=True):
        if arg.is_Number:
            assert arg >= 0
            args.append(sqrt(arg))
        else:
            arg = axiom.is_Square(arg)
            args.append(arg)
    
    return Equal(self, Mul(*args) ** 2, evaluate=evaluate)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(4 * (x + y) ** 2)
    
    Eq << Eq[-1].this.find(Pow).apply(algebra.square.to.add)
    
    Eq << Eq[-1].this.find(Pow).apply(algebra.square.to.add)
    
    
        
if __name__ == '__main__':
    prove()

