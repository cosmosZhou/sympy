from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(self):
    eqs = axiom.is_And(self)
    
    for i, eq in enumerate(eqs): 
        if isinstance(eq, ForAll):
            break
    else:
        return
        
    forall = eqs.pop(i)
    
    function, *limits = forall.args
    
    i, a, b = axiom.limit_is_Interval(limits)
    
    try:
        while eqs:
            j = eqs.index(function._subs(i, b))
            del eqs[j]
            b += 1
    except:
        return    
        
    return Equivalent(self, ForAll[i:a:b](function))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)    
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(oo,))
    
    Eq << apply(And(ForAll[i:0:n](x[i] > 0), x[n] > 0, x[n + 1] > 0))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[-1])
    
    Eq <<= Eq[-2].this.rhs.apply(algebra.forall.given.et, cond={n + 1}), Eq[-1].this.rhs.apply(algebra.forall.imply.et.split, cond={n + 1})
    
    Eq <<= Eq[-2].this.rhs.apply(algebra.forall.given.et, cond={n}), Eq[-1].this.rhs.args[1].apply(algebra.forall.imply.et.split, cond={n})


if __name__ == '__main__':
    prove()

