from axiom.utility import prove, apply
from sympy import Symbol, Or
import axiom
from sympy.logic.boolalg import Sufficient
from axiom import algebre


@apply(imply=True)
def apply(*given):
    is_imply_P, is_imply_Q = given
    x, p = axiom.is_Sufficient(is_imply_P)    
    y, q = axiom.is_Sufficient(is_imply_Q)
    
    return Sufficient(x & y, p & q)


@prove
def prove(Eq):
    p = Symbol.p(real=True, given=True)
    q = Symbol.q(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Sufficient(x > 0, a > 0), Sufficient(y > 0, b > 0))

    Eq << Eq[-1].split()
    
    Eq <<= Sufficient((x > 0) & (y > 0), x > 0, plausible=True), Sufficient((x > 0) & (y > 0), y > 0, plausible=True)
    
    Eq <<= algebre.sufficient.sufficient.imply.sufficient.transit.apply(Eq[0], Eq[-2]), algebre.sufficient.sufficient.imply.sufficient.transit.apply(Eq[1], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)
