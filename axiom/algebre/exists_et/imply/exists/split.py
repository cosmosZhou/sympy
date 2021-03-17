from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, index=None):
    et, *limits = axiom.exists_et(given)
    eqs = et.args
    if index is None:
        eqs = tuple(Exists(eq, *limits)for eq in eqs)
        return eqs
    eq = eqs[index]
    return Exists(eq, *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    
    Eq << apply(Exists[x:2:b]((x <= 3) & (f(x) >= 1)), index=0)
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]    


if __name__ == '__main__':
    prove(__file__)

