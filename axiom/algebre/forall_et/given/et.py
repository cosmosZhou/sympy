from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given): 
    et, *limits = axiom.forall_et(given)    
    return And(*(ForAll(eq, *limits) for eq in et.args))


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
    
    Eq << algebre.et.imply.cond.apply(Eq[1])
    
    Eq << algebre.forall_et.given.forall.apply(Eq[0])

    
if __name__ == '__main__':
    prove(__file__)

