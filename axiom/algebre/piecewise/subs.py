from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(piecewise, index=None):
    if index is None:
        for index, (expr, cond) in enumerate(piecewise.args):
            if cond.is_Equal:
                break
        
        if not cond.is_Equal:
            for index, (expr, cond) in enumerate(piecewise.args):
                if cond.is_And:
                    break
            
    else:
        expr, cond = piecewise.args[index]
    
    if cond.is_And:
        for eq in cond.args:
            if eq.is_Equal: 
                break
    else:
        eq = cond
            
    lhs, rhs = axiom.is_Equal(eq)
    expr = expr._subs(lhs, rhs)
    ec = [*piecewise.args]
    ec[index] = (expr, cond)
    return Equality(piecewise, piecewise.func(*ec))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    g = Function.g(nargs=(k,), shape=(), real=True)
    f = Function.f(nargs=(k,), shape=(), real=True)
    h = Function.h(nargs=(k,), shape=(), real=True)
     
    Eq << apply(Piecewise((g(x), Equality(x, y) & (h(y) > 0)), (f(x), Contains(y, A)), (h(x), True)))
    
    p = Symbol.p(Eq[0].lhs)
    Eq << p.this.definition
    
    Eq << algebre.equal.imply.ou.general.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[2].apply(algebre.et.imply.et.subs, split=False, index=2)
    
    Eq << algebre.ou.imply.equal.general.apply(Eq[-1], wrt=p)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.back)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.front)
    
    Eq << Eq[0].this.rhs.apply(algebre.piecewise.invert)
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])
    
    Eq << Eq[-1].this.rhs.subs(Eq[1])
    

if __name__ == '__main__':
    prove(__file__)

