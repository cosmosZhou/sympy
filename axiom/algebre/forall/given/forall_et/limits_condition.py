from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom
from sympy.concrete.limits import limits_condition


@apply
def apply(imply):
    fn, *limits = axiom.is_ForAll(imply)
    cond = limits_condition(limits)
    return ForAll(fn & cond, *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](f(x) > 0))  
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[1])    
    


if __name__ == '__main__':
    prove(__file__)

