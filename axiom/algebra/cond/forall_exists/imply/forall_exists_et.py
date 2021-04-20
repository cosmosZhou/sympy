from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(*given):
    cond, exists = given
    (fn, *limits_e), *limits_f = axiom.forall_exists(exists)
    
    return ForAll(Exists(cond & fn, *limits_e), *limits_f)


@prove
def prove(Eq): 
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    
    B = Symbol.B(etype=dtype.real)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(f(x, y) > 0, ForAll[y:B](Exists[x:A]((g(x, y) > 0))))
    
    Eq << Eq[-1].this.function.apply(algebra.exists_et.given.et, index=0)
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << algebra.forall.given.cond.apply(Eq[-1])
    

if __name__ == '__main__':
    prove()

