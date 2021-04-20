from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(imply):    
    cond, exists = axiom.is_And(imply)
    if not exists.is_Exists:
        cond, exists = exists, cond
    fn, *limits = axiom.is_Exists(exists)
    
    assert not cond.has(*exists.variables)
    return Exists(fn & cond, *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer)
    f = Function.f(integer=True)    
    g = Function.g(integer=True)

    Eq << apply((f(y) > 0) & Exists[x:A](g(x) > 0))
    
    Eq << algebra.exists_et.imply.exists.split.apply(Eq[-1])
    
    Eq << algebra.et.given.cond.apply(Eq[0])
    
if __name__ == '__main__':
    prove()

