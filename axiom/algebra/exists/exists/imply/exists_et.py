from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_dependent


@apply
def apply(*given):
    exists_x, exists_y = given
    fx, *limits_x = axiom.is_Exists(exists_x)
    fy, *limits_y = axiom.is_Exists(exists_y)
    
    assert not limits_dependent(limits_x, limits_y)
                
    return Exists(fx & fy, *limits_x, *limits_y)


@prove
def prove(Eq): 
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[x:A](f(x, y) > 0), Exists[y:B](g(y, x) > 0))
    
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].this.function.apply(algebra.cond.exists.imply.exists_et)
    

if __name__ == '__main__':
    prove()

