from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_cond


@apply
def apply(imply):
    (fn, *limits_e), *limits_f = axiom.forall_exists(imply)
    cond = limits_cond(limits_f)
    return ForAll(Exists(fn & cond, *limits_e), *limits_f)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](Exists[y:B](f(x, y) > 0)))  
    
    Eq << Eq[1].this.function.simplify()    


if __name__ == '__main__':
    prove()

