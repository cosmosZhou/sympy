from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given): 
    x0, argmax_fx = axiom.is_Equal(given)
    function, limit = axiom.is_ArgMax(argmax_fx)
    assert len(limit) == 1
    x = limit[0]
    fx0 = function._subs(x, x0)
    return GreaterEqual(fx0, function)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))
    
    Eq << algebra.imply.forall_ge.maximize.apply(f(x), (x,))
    
    Eq << algebra.eq.imply.eq.argmax.definition.apply(Eq[0])
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    
if __name__ == '__main__':
    prove()
