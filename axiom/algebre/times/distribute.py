from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(simplify=False)
def apply(self, index=0): 
    args = axiom.is_Times(self, copy=True)
    factor = args.pop(index)
    
    for i, plus in enumerate(args):
        if plus.is_Plus:
            plus = Plus(*(arg * factor for arg in plus.args))
            args[i] = plus
            return Equal(self, Times(*args))


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    r = Symbol.r(real=True)
    Eq << apply(-r * (a - b - c) / d)   
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
