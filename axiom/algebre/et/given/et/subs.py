from sympy import *
from axiom.utility import prove, apply
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from axiom import algebre
import axiom


@apply
def apply(imply, index=-1, invert=None, reverse=False):
    assert imply.is_Boolean
    
    eqs = axiom.is_And(imply)
    
    given = eqs[index]

    imply = []
    if isinstance(index, int):
        if index < 0:
            index += len(eqs)
            
        for i in range(len(eqs)):
            if i == index:
                continue
            imply.append(eqs[i])
    elif isinstance(index, slice):
        given = And(*given)
        start, stop = index.start, index.stop
        if start is None:
            start = 0
        if stop is None:
            stop = len(eqs)
        for i in {*range(len(eqs))} - {*range(start, stop)}:
            imply.append(eqs[i])
    else:
        return
            
    imply = And(*imply) 
    
    if invert:
        old = given.invert()
        new = BooleanFalse()
    else:
        old = given
        new = BooleanTrue()
    
    if reverse:
        old = old.reversed
        
    return imply._subs(old, new) & given


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)) & NotContains(x, S))
    
    Eq << Eq[-1].split()
    
    Eq << Equality(Boole(NotContains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Equal(Piecewise((f(x), Equality(Boole(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.front)
    
    Eq <<= Eq[-1] & Eq[3]
    
    
if __name__ == '__main__':
    prove(__file__)

