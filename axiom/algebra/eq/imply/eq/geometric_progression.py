from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, n=None, a=0):
    a = sympify(a)
    Zn1, rhs = axiom.is_Equal(given)
    r, Zn = axiom.is_Mul(rhs)
    if Zn._subs(n, n + 1) != Zn1:
        r, Zn = Zn, r
        
    assert Zn._subs(n, n + 1) == Zn1
    Za = Zn._subs(n, a)
    if n is None:
        n, *_ = Zn.free_symbols - r.free_symbols
    
    return Equal(Zn, Za * r ** (n - a))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    r = Symbol.r(complex=True)    
    f = Symbol.f(shape=(oo,), complex=True)
    
    Eq << apply(Equal(f[n + 1], r * f[n]), n=n)
    
    Eq << Eq[1].subs(n, 0)
    
    Eq.induction = Eq[1].subs(n, n + 1)
    
    Eq << Eq[1] * r
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.eq.induction.apply(Eq[-1], n=n)


if __name__ == '__main__':
    prove()

