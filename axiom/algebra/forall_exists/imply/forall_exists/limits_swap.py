from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom

@apply
def apply(given):
    y = given.function.variable
    z = Dummy('z', **y.type.dict)
    imply = given.this.function.limits_subs(y, z)
    
    x = given.variable
    imply = imply.limits_subs(x, y)
    
    return imply.this.function.limits_subs(z, x)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), etype=dtype.integer)
    y = Symbol.y(shape=(k,), etype=dtype.integer)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Sx = Symbol.S_x(etype=dtype.integer.set * k)
    Sy = Symbol.S_y(etype=dtype.integer.set * k)
        
    Eq << apply(ForAll[x:Sx](Exists[y:Sy](Equal(f(x), g(y)))))

    Eq << Eq[1].limits_subs(y, Dummy('y', **y.type.dict))

if __name__ == '__main__':
    prove()

