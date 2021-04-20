from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.logic.boolalg import Boolean
from axiom.algebra.forall.imply.et.split import split_forall


@apply
def apply(given, *, cond=None, wrt=None):
    return split_forall(given, cond, wrt)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    d = Symbol.d(real=True, positive=True)
    f = Function.f(integer=True)
    Eq << apply(ForAll[x:-d:d](f(x) > 0), cond=x > 0)
    
    Eq << Eq[-1].apply(algebra.forall.forall.imply.forall.limits_union)

    
if __name__ == '__main__':
    prove()

