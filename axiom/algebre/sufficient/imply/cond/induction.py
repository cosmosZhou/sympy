from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import algebre


@apply
def apply(given, n, start=0):
    start = sympify(start)
        
    fn, fn1 = axiom.is_Sufficient(given)

    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start).simplify()
    
    assert n.domain.min() >= start
    
    return fn    


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
        
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(integer=True, shape=(k,))
    i = Symbol.i(integer=True)
    
    w = Symbol.w(integer=True, shape=(oo, k, k))
    
    S = Symbol.S(etype=dtype.integer * k)
    
    Eq << apply(Sufficient(ForAll[x:S](Contains(x @ MatProduct[i:n](w[i]), S)), ForAll[x:S](Contains(x @ MatProduct[i:n + 1](w[i]), S))), n=n)
    
    Eq << Eq[0].lhs._subs(n, Zero()).copy(plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq[-1], Eq[0], n=n)

        
if __name__ == '__main__':
    prove(__file__)
