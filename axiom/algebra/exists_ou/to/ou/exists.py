from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
import axiom


@apply(given=None)
def apply(imply):
    ou, *limits = axiom.exists_ou(imply)
    
    return Equivalent(imply, Or(*(Exists(eq, *limits) for eq in ou.args)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(integer=True)    
    g = Function.g(integer=True)

    Eq << apply(Exists[x:A]((g(x) > 0) | (f(x) > 0)))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.exists_ou.imply.ou.exists)
    
    Eq << Eq[-1].this.lhs.apply(algebra.exists_ou.given.ou.exists)

if __name__ == '__main__':
    prove()

