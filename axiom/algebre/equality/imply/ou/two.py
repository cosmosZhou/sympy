from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Or
from sympy import Symbol
from sympy.logic.boolalg import BooleanTrue
from sympy.core.function import Function
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.contains import Contains
from axiom import algebre, sets
import axiom


@plausible
def apply(given):
    piecewise, sym = axiom.is_Equal(given)
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise
        
    (e0, c0), (e1, _) = axiom.is_Piecewise(piecewise)
        
    univeralSet = BooleanTrue()
    
    condition = c0 & univeralSet

    invert = condition.invert()
    univeralSet &= invert
     
    cond0 = condition & given.func(sym, e0).simplify()                
                 
    cond1 = univeralSet & given.func(sym, e1).simplify()                
    
    return Or(cond0, cond1)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)

    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equality(p, Piecewise((f(x), Contains(x, A)), (g(x), True))))
    
    Eq << Eq[0].bisect(Contains(x, A)).split()
    
    Eq <<= algebre.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebre.ou.imply.ou.invert.apply(Eq[-1], pivot=1)
    
    Eq <<= Eq[-2].this.args[0].apply(sets.notcontains.equality.imply.et, invert=True), Eq[-1].this.args[0].apply(sets.contains.equality.imply.et)
    
    Eq <<= Eq[-2] & Eq[-1]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].astype(Or)
    

if __name__ == '__main__':
    prove(__file__)

