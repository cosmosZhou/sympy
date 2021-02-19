from sympy import Symbol, Or
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
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
    
    p = Symbol.p(definition=Eq[0].lhs)    
    Eq << p.this.definition
    
    Eq << algebre.equal.imply.ou.general.apply(Eq[-1])
    
    Eq << algebre.ou.imply.equal.general.apply(Eq[-1], wrt=p)
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.piecewise.swap.front)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[1], Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

