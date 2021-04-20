from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
from axiom.algebra.forall.imply.ou import rewrite_as_Or


@apply
def apply(imply):
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(ForAll[x:A](f(x) > 0))
        
    Eq << ~Eq[0]
    
    Eq << algebra.exists.imply.exists_et.single_variable.apply(Eq[-1], simplify=None)
    
    Eq << Eq[-1].this.function.apply(algebra.cond.imply.eq.bool, split=False)
    
    Eq << algebra.cond.imply.eq.bool.invert.apply(Eq[1])
    
    Eq << Eq[-2].this.function.apply(algebra.eq.eq.imply.eq.transit, Eq[-1])


if __name__ == '__main__':
    prove()

