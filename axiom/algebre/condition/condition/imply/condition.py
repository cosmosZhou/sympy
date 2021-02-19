from sympy import *
from axiom.utility import prove, apply
from sympy.logic.boolalg import BooleanTrue, BooleanFalse

def process_given_conditions(*given, invert=None, reverse=False, swap=False):
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given
        
    assert eq.is_Boolean    
    assert f_eq.is_Boolean
    
    eq_original = eq
    if invert:
        eq = eq.invert()
        substituent = BooleanFalse()
    else:
        substituent = BooleanTrue()
    
    if reverse:
        eq = eq.reversed
        
    return eq_original, f_eq._subs(eq, substituent)

@apply
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return f_eq


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))

    Eq << Equality(Boole(NotContains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Equal(Piecewise((f(x), Equality(Boole(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.astype(Piecewise)
    
    Eq << Eq[1].this.lhs.simplify()    
    
    Eq << Eq[-2].subs(Eq[-3])

    
if __name__ == '__main__':
    prove(__file__)

