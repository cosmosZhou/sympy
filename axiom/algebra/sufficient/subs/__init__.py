from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given, index=None, reverse=False):
    p, q = axiom.is_Sufficient(given)
    if index is None:
        if p.is_Equal:
            old, new = p.args
        else:
            eqs = axiom.is_And(p)
            for eq in eqs:
                if eq.is_Equal:                    
                    old, new = eq.args
                    break
    else:
        eqs = axiom.is_And(p)
        old, new = axiom.is_Equal(eqs[index])
                 
    if reverse:
        old, new = new, old
    q = q._subs(old, new)
    return Equivalent(given, Sufficient(p, q), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)    
    A = Symbol.A(etype=dtype.real)
    y = Symbol.y(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(Sufficient(Equal(f(x), x + 1) & Contains(x, A), Equal(g(f(x)), y)))
    
    Eq.sufficient, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[-1])
    
    Eq << Eq.sufficient.this.lhs.apply(algebra.sufficient.imply.sufficient.et, index=0)
    
    Eq << Eq[-1].this.lhs.rhs.apply(algebra.eq.cond.imply.cond.subs)
    
    Eq << Eq.necessary.this.rhs.apply(algebra.sufficient.imply.sufficient.et, index=0)
    
    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

        
if __name__ == '__main__':
    prove()

from . import bool