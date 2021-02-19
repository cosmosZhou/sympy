from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, n=None, m=None, start=0):
    start = sympify(start)
    f0, f1, sufficient = given
    axiom.is_Equal(f0)
    axiom.is_Equal(f1)
    fm, fm2 = axiom.is_Sufficient(sufficient)

    _fm = fm
    fm = fm._subs(n, n - 2)    
    
    assert fm._subs(m, m + 2) == fm2
    assert fm._subs(m, start) == f0
    assert fm._subs(m, start + 1) == f1
    assert m.domain.min() == start
    
    return fm, _fm


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    m = Symbol.m(integer=True, positive=True, given=False)
    f = Symbol.f(real=True, shape=(oo, oo))
    g = Symbol.g(real=True, shape=(oo, oo))
    
    Eq << apply(Equal(f[n, 1], g[n, 1]), Equal(f[n, 2], g[n, 2]), Sufficient(Equal(f[n + 2, m], g[n + 2, m]), Equal(f[n, m + 2], g[n, m + 2])), start=1, n=n, m=m)
    
    Eq << Eq[2].subs(m, 2 * m)
    
    Eq << algebre.equal.sufficient.imply.equal.double.induction.apply(Eq[1], Eq[-1], n=m, start=1, x=n + 2, return_hypothesis=False)
    
    Eq << Eq[-1].forall((m,))
    
    Eq << Eq[2].subs(m, 2 * m - 1)

    Eq << algebre.equal.sufficient.imply.equal.double.induction.apply(Eq[0], Eq[-1], n=m, start=1, x=n + 2, return_hypothesis=False)
    
    Eq << Eq[-1].forall((m,))
    
    Eq << Eq[3].bisect(Equal(m % 2, 0)).split()
    
    _m = Eq[-1].variable
    Eq <<= Eq[-2].limits_subs(_m, 2 * _m), Eq[-1].limits_subs(_m, 2 * _m - 1)
    
    Eq << Eq[3].subs(n, n + 2)

            
if __name__ == '__main__':
    prove(__file__)
