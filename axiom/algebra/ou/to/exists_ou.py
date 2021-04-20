from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
import axiom


@apply(given=None)
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
    
    return Equivalent(imply, Exists(Or(*eqs), *limits))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    
    f = Function.f(integer=True)    
    g = Function.g(integer=True)

    Eq << apply(Or(Exists[x:A]((g(x) > 0)), Exists[x:A](f(x) > 0)))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])
    
    Eq << Eq[-2].this.rhs.apply(algebra.exists_ou.given.ou.exists)
    
    Eq << Eq[-1].this.rhs.apply(algebra.exists_ou.imply.ou.exists)

if __name__ == '__main__':
    prove()

