from axiom.utility import prove, apply
from sympy import *
from axiom import algebre


@apply
def apply(given, *limits):
    assert given.is_Subset
    fx, A = given.args
    
    return Subset(UNION(fx, *limits).simplify(), A)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)
   
    Eq << apply(Subset(x[i], A), (i, 0, m))
    
    Eq.initial = Eq[-1].subs(m, 1)
    
    Eq << Eq[0].subs(i, 0)
    
    Eq.induction = Eq[1].subs(m, m + 1)
        
    Eq << Eq[0].subs(i, m)
    
    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq.induction.induct(imply=True)
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], n=m, start=1, simplify=None)    
    
if __name__ == '__main__':
    prove(__file__)

