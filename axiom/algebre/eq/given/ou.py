from sympy import *
from axiom.utility import prove, apply
from sympy.logic.boolalg import BooleanTrue
from axiom import algebre
import axiom


@apply
def apply(imply):
    piecewise, sym = axiom.is_Equal(imply)
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
         
        eq = condition & imply.func(sym, expr).simplify()                
        eq.equivalent = None
        args.append(eq)
                 
    return Or(*args)


@prove
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
    
    Eq << algebre.ou.imply.eq.general.apply(Eq[1], wrt=p)
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove(__file__)

