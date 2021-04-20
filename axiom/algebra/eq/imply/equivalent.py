from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


# given: A = B
# A >> B
@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
    lhs = axiom.is_Bool(lhs) 
    rhs = axiom.is_Bool(rhs)
    return Equivalent(lhs, rhs)


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    f = Function.f(shape=())

    Eq << apply(Equal(Bool(a > b), Bool(f(a) > f(b))))
    
    Eq << Eq[0] * Eq[0].lhs
    
    Eq << algebra.pow.to.bool.apply(Eq[-1].lhs)
    
    Eq << Eq[-2] - Eq[-1]
    
    Eq << algebra.is_zero.imply.eq.apply(Eq[-1])
    
    Eq.sufficient = algebra.eq.imply.sufficient.bool.apply(Eq[-1])

    Eq << Eq[0] * Eq[0].rhs
    
    Eq << algebra.pow.to.bool.apply(Eq[0].rhs ** 2)
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)
    
    Eq << algebra.eq.imply.sufficient.bool.apply(Eq[-1])
    
    Eq <<= Eq.sufficient & Eq[-1]


if __name__ == '__main__':
    prove()

