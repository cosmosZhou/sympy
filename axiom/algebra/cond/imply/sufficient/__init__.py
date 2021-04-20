from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Sufficient(cond, given)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(algebra.sufficient.given.ou)
    
    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)

    
if __name__ == '__main__':
    prove()

from . import bisected
