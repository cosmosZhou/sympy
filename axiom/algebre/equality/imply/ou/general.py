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
     
    piecewise = axiom.is_Piecewise(piecewise)
    
    univeralSet = BooleanTrue()
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


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equality(p, Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))))
    
    Eq << Eq[0].bisect(Contains(x, A)).split()
    
    Eq <<= algebre.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebre.ou.imply.ou.invert.apply(Eq[-1], pivot=1)
    
    Eq <<= Eq[-2].this.args[0].apply(sets.notcontains.equality.imply.et, invert=True), Eq[-1].this.args[0].apply(sets.contains.equality.imply.et)
    
    Eq <<= Eq[-2] & Eq[-1]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].astype(Or)
    
    Eq << Eq[-1].this.args[0].args[0].apply(algebre.equality.imply.ou.two)
    
    Eq << Eq[-1].this.args[0].astype(Or)
    

if __name__ == '__main__':
    prove(__file__)

