from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(self):
    function, *limits = axiom.is_Exists(self)
    assert len(limits) == 2
    limit0, limit1 = limits
    
    x, *domain_x = limit0
    y, *domain_y = limit1
    
    for s in domain_x:
        assert not s._has(y)
        
    limits = limit1, limit0
    return Exists(function, *limits)


@prove
def prove(Eq): 
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Exists[x:A, y:f(y) > 0](g(x, y) > 0))
    
    Eq << ~Eq[-1]
    
    Eq <<= algebra.forall.exists.imply.exists_et.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    prove()

