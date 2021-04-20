from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given, index=None, invert=False):    
    p, q = axiom.is_Sufficient(given)
    if index is None:
        cond = p
    else:
        eqs = axiom.is_And(p)
        cond = eqs[index]
        
    if invert:
        old = cond.invert()
        new = S.false
    else:
        old = cond
        new = S.true
        
    q = q._subs(old, new)
    return Equivalent(given, Sufficient(p, q), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)    
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Sufficient(Equal(f(x), x + 1) & Contains(x, A), 
                           Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)), 
                           index=0)
    
    Eq << Equivalent(Sufficient(Equal(f(x), x + 1) & Contains(x, A),
                                Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),
                      
                     Sufficient(Equal(Bool(Equal(f(x), x + 1)), 1) & Contains(x, A),
                                Equal(Piecewise((g(x), Equal(Bool(Equal(f(x), x + 1)), 1)), (g(y), True)), y)),
                      
                     plausible=True)
    
    Eq << Eq[-1].this.find(Bool).definition

    Eq << Eq[-1].this.find(Bool).definition
    
    Eq << Eq[1].this.rhs.apply(algebra.sufficient.subs)
    
    Eq << Eq[-1].this.find(Bool).definition

        
if __name__ == '__main__':
    prove()
