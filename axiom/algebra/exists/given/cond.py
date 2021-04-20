from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(imply):
    function, *limits = axiom.is_Exists(imply)
    assert all(len(limit) == 1 for limit in limits)    
    return function


@prove
def prove(Eq):    
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Exists[e](f(e) > 0))
    
    Eq << algebra.cond.imply.exists.apply(Eq[1], wrt=e)


if __name__ == '__main__':
    prove()

