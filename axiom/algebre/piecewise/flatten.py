from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(piecewise, index=-1):
    expr, cond = piecewise.args[index]
    _ec = axiom.is_Piecewise(expr)
     
    _ec = tuple((e, c & cond) for e, c in _ec)
    ec_before = piecewise.args[:index]
      
    if index < 0:
        index += len(piecewise.args)
        
    ec_after = piecewise.args[index + 1:]
    
    return Equality(piecewise, piecewise.func(*ec_before + _ec + ec_after))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    f = Function.f(nargs=(k,), shape=(), real=True)
    g = Function.g(nargs=(k,), shape=(), real=True)
    h = Function.h(nargs=(k,), shape=(), real=True)
     
#     Eq << apply(Piecewise((f(x), Contains(x, A)), (Piecewise((g(x), Contains(x, B)), (h(x), True)), True)))
    Eq << apply(Piecewise((Piecewise((g(x), Contains(x, B)), (h(x), True)), Contains(x, A)), (f(x), True)), index=0)
    
    p = Symbol.p(Eq[0].lhs)

    Eq << p.this.definition
    
    Eq << algebre.equal.imply.ou.general.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].args[0].apply(algebre.equal.imply.ou.two)
    
    Eq << Eq[-1].this.args[0].astype(Or)
    
    Eq << algebre.ou.imply.equal.general.apply(Eq[-1], wrt=p)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.front)
    
    Eq << Eq[-1].this.lhs.apply(algebre.piecewise.swap.back)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[1], Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

