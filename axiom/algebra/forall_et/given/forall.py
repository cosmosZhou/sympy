from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given): 
    et, *limits = axiom.forall_et(given)    
    return tuple(ForAll(eq, *limits) for eq in et.args)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(ForAll[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))
    
    Eq <<= Eq[1] & Eq[2] & Eq[3]

    
if __name__ == '__main__':
    prove()

