from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from sympy.concrete.limits import limits_cond


@apply
def apply(given, index=0):
    assert index == 0
    function, *limits = axiom.is_ForAll(given)
    
    assert len(limits) > 1
    
    limit, *limits = limits
    cond = limits_cond((limit,))
    return ForAll(function | cond.invert(), *limits)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)    
    f = Function.f(real=True)

    Eq << apply(ForAll[x:A, y:B](f(x, y) > 0))
    
    Eq << Eq[1].this.function.apply(algebra.ou.given.forall, pivot=1)
    

if __name__ == '__main__':
    prove()

