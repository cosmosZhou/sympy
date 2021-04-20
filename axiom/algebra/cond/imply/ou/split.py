from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, *, cond=None):
    assert cond.is_boolean
    return Or(given & cond.invert(), cond) 


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    f = Function.f(integer=True, shape=())
    g = Function.g(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=g(e) > 0)
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()

