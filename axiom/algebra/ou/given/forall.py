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
    
    Eq << algebra.forall.imply.ou.apply(Eq[1])
    
if __name__ == '__main__':
    prove()

