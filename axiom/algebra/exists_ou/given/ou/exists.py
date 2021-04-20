from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
import axiom


@apply
def apply(imply):
    ou, *limits = axiom.exists_ou(imply)
    
    return Or(*(Exists(eq, *limits) for eq in ou.args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real, given=True)
    
    f = Function.f(integer=True)    
    g = Function.g(integer=True)

    Eq << apply(Exists[x:A]((g(x) > 0) | (f(x) > 0)))
    
    Eq << ~Eq[0]
    
    Eq << algebra.forall_et.imply.et.apply(Eq[-1])
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    prove()

