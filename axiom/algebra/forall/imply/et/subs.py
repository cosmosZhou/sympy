from axiom.utility import prove, apply
from sympy import *
import axiom
from sympy.concrete.limits import limits_dict
from axiom import algebra


@apply
def apply(given, old, new):
    cond, *limits = axiom.is_ForAll(given)
    
    limitsDict = limits_dict(limits)
    assert old in limitsDict
    assert new in limitsDict[old]
    
    return given & cond._subs(old, new)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    A = Symbol.A(etype=dtype.integer)
    x0 = Symbol.x0(domain=A)
    
    Eq << apply(ForAll[x:A](Contains(f(x), s)), x, x0)
    
    Eq << algebra.et.given.cond.apply(Eq[1])
    
    Eq << algebra.forall.imply.cond.subs.apply(Eq[0], x, x0)
    

if __name__ == '__main__':
    prove()

