from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
from axiom.algebra.forall.imply.ou import rewrite_as_Or


@apply(given=None)
def apply(imply):
    return Equivalent(imply, rewrite_as_Or(imply))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](f(x) > 0))
    
    Eq << algebra.equivalent.given.sufficient.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.forall.imply.ou)
    
    Eq << Eq[-1].this.rhs.apply(algebra.forall.given.ou)


if __name__ == '__main__':
    prove()

