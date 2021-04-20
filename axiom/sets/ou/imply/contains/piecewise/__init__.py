from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from axiom.sets.ou.imply.contains.piecewise.two import expr_cond_pair

    
@apply
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    
    return Contains(Piecewise(*expr_cond_pair(Contains, or_eqs, wrt)).simplify(), wrt)            


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)
    
    S = Symbol.S(etype=dtype.real * k, given=True)
    
    Eq << apply(Contains(f(x), S) & Contains(x, A) | Contains(g(x), S) & Contains(x, B - A) | Contains(h(x), S) & NotContains(x, A | B), wrt=S)
    
    Eq << Eq[0].this.args[1].args[1].apply(sets.contains.imply.et.split.complement, simplify=None)
    
    Eq << Eq[-1].this.args[2].args[1].apply(sets.notcontains.imply.et.split.union, simplify=None)
    
    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotContains(x, A))
    
    Eq << Eq[-1].this.args[0].args[0].apply(sets.ou.imply.contains.piecewise.two, wrt=S)
    
    Eq << Eq[-1].apply(sets.ou.imply.contains.piecewise.two, wrt=S)    

        
if __name__ == '__main__':
    prove()

from . import rhs