from sympy import *
from axiom.utility import prove, apply
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from axiom import algebre
import axiom


@apply
def apply(imply):    
    cond, exists = axiom.is_And(imply)
    fn, *limits = axiom.is_Exists(exists)
    
    assert not cond.has(*exists.variables)
    return Exists(fn & cond, *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)    
    g = Function.g(shape=(), integer=True)

    Eq << apply((f(y) > 0) & Exists[x:A](g(x) > 0))
    
    Eq << Eq[-1].split()
    
    Eq << Eq[0].split()
    
if __name__ == '__main__':
    prove(__file__)

