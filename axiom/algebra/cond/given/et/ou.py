from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    
    _eq = cond.invert()
    return And(Or(cond, given), Or(_eq, given))

@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)
    
    Eq << algebra.et.imply.ou.collect.apply(Eq[1], cond=Eq[0])

if __name__ == '__main__':
    prove()

