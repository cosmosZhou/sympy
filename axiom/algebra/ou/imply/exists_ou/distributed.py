from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
import axiom


@apply
def apply(imply):
    exists = axiom.is_Or(imply)
    limits = None
    eqs = []
    for exist in exists:
        fn, *_limits = axiom.is_Exists(exist)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)
    
    return Exists(Or(*eqs), *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(integer=True)    
    g = Function.g(integer=True)

    Eq << apply(Or(Exists[x:A]((g(x) > 0)), Exists[x:A](f(x) > 0)))
    
    Eq << algebra.exists_ou.given.ou.exists.apply(Eq[1])
    
if __name__ == '__main__':
    prove()

