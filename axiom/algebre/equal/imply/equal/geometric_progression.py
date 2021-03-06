from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, Product
from sympy.core.function import Function
import axiom
from sympy.sets.sets import Interval
from axiom import algebre
from sympy.core.sympify import sympify
from sympy.core.numbers import oo


@apply(imply=True)
def apply(given, n=None, a=0):
    a = sympify(a)
    Zn1, rhs = axiom.is_Equal(given)
    r, Zn = axiom.is_Times(rhs)
    if Zn._subs(n, n + 1) != Zn1:
        r, Zn = Zn, r
        
    assert Zn._subs(n, n + 1) == Zn1
    Za = Zn._subs(n, a)
    if n is None:
        n, *_ = Zn.free_symbols - r.free_symbols
    
    return Equality(Zn, Za * r ** (n - a))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    r = Symbol.r(complex=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Symbol.f(shape=(oo,), complex=True)
    
    Eq << apply(Equality(f[n + 1], r * f[n]), n=n)
    
    Eq << Eq[1].subs(n, 0)
    
    Eq.induction = Eq[1].subs(n, n + 1)
    
    Eq << Eq[1] * r
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.sufficient.imply.equal.induction.apply(Eq[-1], n=n)


if __name__ == '__main__':
    prove(__file__)

