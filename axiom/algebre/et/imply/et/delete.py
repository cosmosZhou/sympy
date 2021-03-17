from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given, index=0):
    and_eqs = axiom.is_And(given)

    del and_eqs[index]
    
    return And(*and_eqs)            


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    
    Eq << apply(Unequal(x, y) & Equality(f(x), g(y)) & (a > b), index=0)
    
    Eq << algebre.et.imply.cond.apply(Eq[0])
    
    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove(__file__)

