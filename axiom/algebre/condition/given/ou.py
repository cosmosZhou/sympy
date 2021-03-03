from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import sets, algebre

    
@apply
def apply(imply):
    piecewise, sym = axiom.is_BinaryCondition(imply)
    if not piecewise.is_Piecewise:
        imply = imply.reversed
        piecewise, sym = imply.args
     
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
         
        eq = condition & imply.func(expr, sym).simplify()                
        eq.equivalent = None
        args.append(eq)
                 
    return Or(*args)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    
    f = Function.f(nargs=(k,), shape=(), real=True)
    g = Function.g(nargs=(k,), shape=(), real=True)
    h = Function.h(nargs=(k,), shape=(), real=True)
    p = Symbol.p(real=True, shape=(), given=True)
    
    Eq << apply(LessThan(Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True)), p))

    Eq << algebre.ou.imply.less_than.general.apply(Eq[1], wrt=p)

        
if __name__ == '__main__':
    prove(__file__)

