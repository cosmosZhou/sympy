from axiom.utility import prove, apply
from sympy import Symbol
from sympy.core.function import Function
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from axiom import sets, algebre

from axiom.sets.ou.imply.contains.two import expr_cond_pair
from sympy.core.relational import GreaterThan

    
@apply(imply=True)
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    
    return GreaterThan(Piecewise(*expr_cond_pair(GreaterThan, or_eqs, wrt)).simplify(), wrt)




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    
    p = Symbol.p(shape=(k,), real=True, given=True)
    
    Eq << apply(GreaterThan(f(x), p) & Contains(x, A) | GreaterThan(g(x), p) & Contains(x, B - A) | GreaterThan(h(x), p) & NotContains(x, A | B), wrt=p)
    
    Eq << Eq[0].this.args[1].args[1].apply(sets.contains.imply.et.where.complement, simplify=None)
    
    Eq << Eq[-1].this.args[2].args[1].apply(sets.notcontains.imply.et.where.union, simplify=None)
    
    Eq << Eq[-1].apply(algebre.ou.imply.ou.collect, factor=NotContains(x, A))
    
    Eq << Eq[-1].this.args[0].args[0].apply(algebre.ou.imply.greater_than.two, wrt=p)
    
    Eq << Eq[-1].apply(algebre.ou.imply.greater_than.two, wrt=p)   
    
        
if __name__ == '__main__':
    prove(__file__)

