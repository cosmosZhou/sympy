from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    
    return And(Or(cond, given), Or(cond.invert(), given))


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)
    
    Eq << algebra.et.given.cond.apply(Eq[1])
    
    Eq << algebra.ou.given.cond.apply(Eq[-2], index=1)
    
    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)

    
if __name__ == '__main__':
    prove()

