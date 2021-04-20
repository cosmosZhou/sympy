from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
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
        new = S.BooleanFalse
    else:
        old = given
        new = S.BooleanTrue
    
    if reverse:
        old = old.reversed
        
    return imply._subs(old, new) & given


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)    
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)) & NotContains(x, S))
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << Equal(Bool(NotContains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Equal(Piecewise((f(x), Equal(Bool(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.definition
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.front)
    
    Eq <<= Eq[-1] & Eq[3]
    
    
if __name__ == '__main__':
    prove()

from . import forall_eq