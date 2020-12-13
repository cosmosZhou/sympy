from axiom.utility import plausible
from sympy.logic.boolalg import Or
from sympy import Symbol
from sympy.core.function import Function
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from axiom import sets

def expr_cond_pair(cls, or_eqs, wrt, reverse=None):
    expr = []
    cond = []
    for eq in or_eqs:
        and_eqs = axiom.is_And(eq)
        eq, condition = and_eqs
        if not isinstance(eq, cls):
            condition, eq = and_eqs         
        assert isinstance(eq, cls)
        if wrt == eq.rhs:
            expr.append(eq.lhs)
        elif reverse and wrt == eq.lhs:
            expr.append(eq.rhs)
        else:
            assert isinstance(cond, cls)
            if wrt == cond.rhs:
                expr.append(cond.lhs)
            elif reverse and wrt == cond.lhs:
                expr.append(cond.rhs)
            else:
                return
            condition = eq
        for c in cond:
            assert (condition & c).is_BooleanFalse

        cond.append(condition)
    ec = [[e, c] for e, c in zip(expr, cond)]
    ec[-1][1] = True
    return ec

@plausible
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    
    assert len(or_eqs) == 2
    return Contains(Piecewise(*expr_cond_pair(Contains, or_eqs, wrt)).simplify(), wrt)            


from axiom.utility import check


@check
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
    
    Eq <<= Eq[-2].apply(sets.notcontains.notcontains.imply.et, invert=True, swap=True), Eq[-1].apply(sets.contains.notcontains.imply.et) 
    
    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-2].astype(Or)
        
if __name__ == '__main__':
    prove(__file__)

