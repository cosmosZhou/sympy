from sympy import Symbol, Or, Equality
from axiom.utility import prove, apply

from sympy.core.function import Function
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from axiom import sets, algebre

from axiom.sets.ou.imply.contains.two import expr_cond_pair
from sympy.core.relational import LessThan
from sympy.logic.boolalg import BooleanTrue

    
@apply(given=True)
def apply(imply):
    piecewise, sym = axiom.is_BinaryCondition(imply)
     
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

