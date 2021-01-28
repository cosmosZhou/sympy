from sympy import Symbol, Or
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
from axiom import algebre
import axiom


@apply(imply=True)
def apply(piecewise, index=None):
    if index is None:
        for index, (expr, cond) in enumerate(piecewise.args):
            if cond.is_Equal:
                break
    else:
        expr, cond = piecewise.args[index]
    
    lhs, rhs = axiom.is_Equal(cond)
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
     
    Eq << apply(Piecewise((g(x), Equality(x, y)), (f(x), Contains(y, A)), (h(x), True)))
    
    p = Symbol.p(definition=Eq[0].lhs)
    Eq << p.this.definition
    
    Eq << algebre.equal.imply.ou.general.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(algebre.equal.condition.imply.et, delta=False, swap=True)
    
    Eq.p_definition = algebre.ou.imply.equal.general.apply(Eq[-1], wrt=p)
    
    Eq << algebre.imply.equal.piecewise.swap.front.apply(Eq.p_definition.lhs)
    
    Eq << Eq[-1].this.rhs.args[0].cond.astype(Or)    
    
    Eq << Eq[-1].this.rhs.args[0].cond.collect(Equality(x, y))
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.p_definition, Eq[-1])
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[1], Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

