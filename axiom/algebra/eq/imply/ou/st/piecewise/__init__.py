from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom

def piecewise_to_ou(given):
    piecewise, sym = given.args
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise
     
    piecewise = axiom.is_Piecewise(piecewise)
    
    univeralSet = S.BooleanTrue
    args = []
    
    for expr, cond in piecewise:
        condition = cond & univeralSet
        condition.equivalent = None
         
        if not cond:
            invert = condition.invert()
            univeralSet &= invert
            univeralSet.equivalent = None
         
        eq = condition & given.func(sym, expr).simplify()                
        eq.equivalent = None
        args.append(eq)
                 
    return Or(*args)
    
@apply
def apply(given):
    assert given.is_Equal
    return piecewise_to_ou(given)

@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equal(p, Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))))
    
    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Contains(x, A))
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)
    
    Eq <<= Eq[-2].this.args[0].apply(algebra.cond.cond.imply.et, invert=True, swap=True), Eq[-1].this.args[0].apply(algebra.cond.cond.imply.et, swap=True)
    
    Eq <<= Eq[-2] & Eq[-1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
    
    Eq << Eq[-1].this.args[0].args[0].apply(algebra.eq.imply.ou.st.piecewise.two)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
    

if __name__ == '__main__':
    prove()

from . import two