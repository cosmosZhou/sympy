from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


# given: f(a) != f(b) or a = b
# ForAll[a: a!=b](f(a) != f(b)) 
@apply
def apply(given, pivot=0, wrt=None):
    conds = axiom.is_Or(given)
    
    eq = conds.pop(pivot)
    
    if wrt is None:
        wrt = eq.wrt
            
    assert eq._has(wrt)

    cond = eq.invert()
    
    return ForAll[wrt:cond](given.func(*conds))            


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))    
    
    f = Function.f(complex=True, shape=())
    g = Function.g(complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equal(x, y), pivot=1)
    
    Eq << Eq[0].apply(algebra.cond.imply.et.forall, cond=Equal(x, y))
    
    Eq << sets.imply.forall.complement.apply(y, x=x)
    
    Eq <<= Eq[-2] & Eq[-1]
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1], index=0)
    
    Eq << sets.ne.to.contains.apply(x, y)
    
    Eq << ForAll[x: Equal(Bool(Contains(x, Eq[2].limits[0][1])), 1)](Eq[2].function, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].lhs.definition
    
    Eq << algebra.equivalent.cond.imply.cond.apply(Eq[-2].reversed, Eq[-1])
    
    Eq << Eq[-1].this.limits[0][1].lhs.definition

    
if __name__ == '__main__':
    prove()

