from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def flatten(piecewise, index=None):
    if index is None:
        for index, (e, c) in enumerate(piecewise.args):
            if e.is_Piecewise:
                break
        else:
            return piecewise
        
        _piecewise = flatten(piecewise, index)
        if _piecewise is piecewise:
            return piecewise
        return flatten(_piecewise)
        
    expr, cond = piecewise.args[index]
    _ec = axiom.is_Piecewise(expr)
     
    _ec = tuple((e, c & cond) for e, c in _ec)
    ec_before = piecewise.args[:index]
      
    if index < 0:
        index += len(piecewise.args)
        
    ec_after = piecewise.args[index + 1:]
    return piecewise.func(*ec_before + _ec + ec_after)


@apply
def apply(piecewise, index=None):    
    return Equal(piecewise, flatten(piecewise, index))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    B = Symbol.B(etype=dtype.real * k)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)
     
#     Eq << apply(Piecewise((f(x), Contains(x, A)), (Piecewise((g(x), Contains(x, B)), (h(x), True)), True)))
    Eq << apply(Piecewise((Piecewise((g(x), Contains(x, B)), (h(x), True)), Contains(x, A)), (f(x), True)))
    
    p = Symbol.p(Eq[0].lhs)

    Eq << p.this.definition
    
    Eq << algebra.eq.imply.ou.st.piecewise.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].args[0].apply(algebra.eq.imply.ou.st.piecewise)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)
    
    Eq << algebra.ou.imply.eq.apply(Eq[-1], wrt=p)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.front)
    
    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.back)
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-1])
    

if __name__ == '__main__':
    prove()

