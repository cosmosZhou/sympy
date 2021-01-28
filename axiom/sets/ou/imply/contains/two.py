from axiom.utility import prove, apply
from sympy.logic.boolalg import Or, And
from sympy import Symbol
from sympy.core.function import Function
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from axiom import algebre

def expr_cond_pair(cls, or_eqs, wrt, reverse=None):
    expr = []
    cond = []
    for eq in or_eqs:
        and_eqs = axiom.is_And(eq)
        
        for i, eq in enumerate(and_eqs):
            if isinstance(eq, cls):
                if wrt == eq.rhs:
                    expr.append(eq.lhs)
                    break         
                elif reverse and wrt == eq.lhs:
                    expr.append(eq.rhs)
                    break
                    
        assert eq is and_eqs[i]
        assert isinstance(eq, cls)
        del and_eqs[i]
        condition = And(*and_eqs)
        
        for c in cond:
            assert (condition & c).is_BooleanFalse

        cond.append(condition)
    ec = [[e, c] for e, c in zip(expr, cond)]
    ec[-1][1] = True
    return ec

@apply(imply=True)
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    
    assert len(or_eqs) == 2
    return Contains(Piecewise(*expr_cond_pair(Contains, or_eqs, wrt)).simplify(), wrt)            




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    
    S = Symbol.S(etype=dtype.real * k, given=True)
    
    Eq << apply(Contains(f(x), S) & Contains(x, A) | Contains(g(x), S) & NotContains(x, A), wrt=S)
    
    Eq << Eq[1].bisect(Contains(x, A)).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]
    
    Eq <<= Eq[-2].apply(algebre.condition.condition.imply.et, invert=True, swap=True), Eq[-1].apply(algebre.condition.condition.imply.et, swap=True) 
    
    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-2].astype(Or)
        
if __name__ == '__main__':
    prove(__file__)

