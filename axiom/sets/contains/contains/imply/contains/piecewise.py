
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy import Symbol, Or, Boole
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from sympy.core.relational import Equal
from axiom import sets


@apply
def apply(*given, piecewise=None):
    S = None
    elements = set()
    for eq in given:
        e, _S = axiom.is_Contains(eq)
        if S is None:
            S = _S
        else:
            assert _S == S
        elements.add(e)
        
    for e, _ in piecewise.args:
        assert e in elements
        
    return Contains(piecewise, S)




@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    h = Function.h(nargs=(), shape=(), real=True)

    piecewise = Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))
                          
    Eq << apply(Contains(f(x), S), Contains(g(x), S), Contains(h(x), S), piecewise=piecewise)
    
    Eq.plausible = Or(Equal(Boole(Contains(f(x), S)), 1) & Contains(x, A),
             Equal(Boole(Contains(g(x), S)), 1) & Contains(x, B - A),
             Equal(Boole(Contains(h(x), S)), 1) & NotContains(x, A | B), plausible=True)
    
    Eq.bool_fx = sets.contains.imply.eq.bool.contains.apply(Eq[0])
    Eq.bool_gx = sets.contains.imply.eq.bool.contains.apply(Eq[1])
    Eq.bool_hx = sets.contains.imply.eq.bool.contains.apply(Eq[2])
    
    Eq << Eq.plausible.subs(Eq.bool_fx).subs(Eq.bool_gx).subs(Eq.bool_hx)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].this.args[0].apply(sets.contains.imply.ou.having.union, complement=True)
    
    Eq << Eq[-1].astype(Or)

    Eq << Eq.plausible.this.args[0].args[1].lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.args[1].args[1].lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.args[2].args[1].lhs.astype(Piecewise)
    
    Eq << sets.ou.imply.contains.general.apply(Eq[-1], wrt=S)

    
if __name__ == '__main__':
    prove(__file__)

