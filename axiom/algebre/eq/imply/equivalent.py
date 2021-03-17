from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


# given: A = B
# A >> B
@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
    lhs = axiom.is_Boole(lhs) 
    rhs = axiom.is_Boole(rhs)
    return Equivalent(lhs, rhs)


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    f = Function.f(shape=())

    Eq << apply(Equality(Boole(a > b), Boole(f(a) > f(b))))
    
    Eq << Eq[0] * Eq[0].lhs
    
    Eq << algebre.power.astype.bool.apply(Eq[-1].lhs)
    
    Eq << Eq[-2] - Eq[-1]
    
    Eq.sufficient = algebre.eq.imply.sufficient.bool.apply(Eq[-1])

    Eq << Eq[0] * Eq[0].rhs
    
    Eq << algebre.power.astype.bool.apply(Eq[0].rhs ** 2)
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << algebre.eq.imply.sufficient.bool.apply(Eq[-1].reversed)
    
    Eq <<= Eq.sufficient & Eq[-1]


if __name__ == '__main__':
    prove(__file__)

