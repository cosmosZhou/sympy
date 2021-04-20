from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_boolean
    
    if wrt is None:
        wrt = cond.wrt
        
    assert not wrt.is_given

    if wrt.is_bounded:
        given = given.forall((wrt,), simplify=False)
    else:
        given = ForAll(given, (wrt,))
    assert given.is_ForAll
    return given.bisect(wrt.domain_conditioned(cond))


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    f = Function.f(real=True)
    Eq << apply(f(e) > 0, cond=e > 0)
    
    Eq << Eq[-1].apply(algebra.forall.forall.imply.forall.limits_union)

    
if __name__ == '__main__':
    prove()

