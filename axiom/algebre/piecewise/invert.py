from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(piecewise, index=0):
    ec = axiom.is_Piecewise(piecewise, copy=True)
    
    _, cond = ec[index]
    
    expr_next, cond_next = ec[index + 1]
    cond_next &= cond.invert()
    
    ec[index + 1] = (expr_next, cond_next)
    return Equality(piecewise, piecewise.func(*ec))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    g = Function.g(nargs=(k,), shape=(), real=True)
    f = Function.f(nargs=(k,), shape=(), real=True)
    h = Function.h(nargs=(k,), shape=(), real=True)
     
    Eq << apply(Piecewise((g(x), Contains(x, A)), (f(x), NotContains(x, B)), (h(x), True)))
    
    p = Symbol.p(Eq[0].lhs)    
    Eq << p.this.definition
    
    Eq << algebre.eq.imply.ou.general.apply(Eq[-1])
    
    Eq << algebre.ou.imply.eq.general.apply(Eq[-1], wrt=p)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.front)
    
    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

