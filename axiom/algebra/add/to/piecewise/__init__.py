from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    args = axiom.is_Add(self, copy=True)
    for i, p in enumerate(args):
        if p.is_Piecewise:
            break
    else:
        return    
    
    del args[i]
    a = Add(*args)    
    ecs = ((e + a, c) for e, c in p.args)
        
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    Eq << apply(Piecewise((f(x), Contains(x, A)), (g(x), True)) + h(x))
    
    Eq << Eq[0].this.rhs.apply(algebra.piecewise.to.add, -h(x))

    
if __name__ == '__main__':
    prove()

from . import st
