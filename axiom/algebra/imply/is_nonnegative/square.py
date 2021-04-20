from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(simplify=False)
def apply(function): 
    assert function.is_real
    square = function ** 2
    square = square.expand()
    return GreaterEqual(square, 0, evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(x + y)
    
    Eq << ((x + y)**2).this.apply(algebra.square.to.add)
    
    Eq << Eq[0].subs(Eq[-1].reversed)
        
if __name__ == '__main__':
    prove()


