from sympy import *
from axiom.utility import prove, apply
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from axiom import algebre


@apply
def apply(imply, given, invert=None, reverse=False):
    assert given.plausible is None
    assert given.is_Boolean
    assert imply.is_Boolean
    
    if invert:
        given = given.invert()
        substituent = BooleanFalse()
    else:
        substituent = BooleanTrue()
    
    if reverse:
        given = given.reversed
        
    return imply._subs(given, substituent)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)), NotContains(x, S))

    Eq << Equality(Boole(NotContains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

    Eq << Equal(Piecewise((f(x), Equality(Boole(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.piecewise.swap.front)
    
    
if __name__ == '__main__':
    prove(__file__)

