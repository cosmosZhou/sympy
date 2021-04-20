from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
import axiom


@apply
def apply(imply, index=-1):
    et, *limits = axiom.exists_et(imply)
    eqs = [*et.args]
    cond = eqs[index]
    del eqs[index]
    
    return And(cond, Exists(And(*eqs), *limits))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Exists[x:A]((g(x) > 0) & (f(x) > 0)))

    Eq << Eq[-1].apply(algebra.cond.exists.imply.exists_et)
    
if __name__ == '__main__':
    prove()

