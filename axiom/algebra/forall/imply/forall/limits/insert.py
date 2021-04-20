from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *limits):
    
    function, *limits_f = axiom.is_ForAll(given)
    
    variables_set = given.variables_set
    for var, *ab in limits:
        assert var not in variables_set
    
    limits = tuple(limits_f) + limits
    return ForAll(function, *limits)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)    
    f = Function.f(real=True)

    Eq << apply(ForAll[x:A](f(x, y) > 0), (y, B))
    
    Eq << Eq[0].this.function.apply(algebra.cond.imply.forall.restrict, (y, B))
    
    Eq << algebra.forall.imply.forall.limits.swap.apply(Eq[-1])
    

if __name__ == '__main__':
    prove()

