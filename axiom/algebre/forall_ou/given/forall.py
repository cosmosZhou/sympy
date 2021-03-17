from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, index=None):
    ou, *limits = axiom.forall_ou(given)
    eqs = ou.args
    
    if index is None:
        eqs = tuple(ForAll(eq, *limits) for eq in eqs)
        return eqs
    
    eq = eqs[index]
    
    return ForAll(eq, *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    
    Eq << apply(ForAll[x:2:b]((x <= 3) | (f(x) >= 1)), index=0)
    
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]    

if __name__ == '__main__':
    prove(__file__)

