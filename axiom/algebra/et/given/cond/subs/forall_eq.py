from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from sympy.concrete.expr_with_limits import ExprWithLimits


@apply
def apply(imply, simplify=True):
    forall_eq, cond = axiom.is_And(imply)
    eq, *limits = axiom.forall_eq(forall_eq)
    limits = tuple(limits)
    old, new = eq.args
    
    for expr in cond.findall(ExprWithLimits):        
        if expr.function._has(old) and expr.limits == limits:            
            break
    else:
        return
        
                        
    function = expr.function._subs(old, new)
    if simplify:
        function = function.simplify()
            
    expr_ = expr.func(function, *limits)    
    if simplify:
        expr_ = expr_.simplify()
        
    cond = cond._subs(expr, expr_)
        
    return forall_eq, cond


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True, shape=(oo,))
    b = Symbol.b(integer=True, shape=(oo,))
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(ForAll[i:n](Equal(a[i], b[i])) & Contains(Sum[i:n](a[i]), S))
    
    Eq << algebra.forall_eq.imply.eq.sum.apply(Eq[-2])
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq <<= Eq[-1] & Eq[1]
    
    
if __name__ == '__main__':
    prove()

