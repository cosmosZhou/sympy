from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol, Sufficient

from sympy.core.numbers import oo
import axiom
from axiom import algebre
from sympy.core.sympify import sympify


@plausible
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


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    m = Symbol.m(integer=True, positive=True)
    f = Symbol.f(real=True, shape=(oo, oo))
    g = Symbol.g(real=True, shape=(oo, oo))
    
    Eq << apply(Equal(f[n, 1], g[n, 1]), Equal(f[n, 2], g[n, 2]), Sufficient(Equal(f[n + 2, m], g[n + 2, m]), Equal(f[n, m + 2], g[n, m + 2])), start=1, n=n, m=m)
    
    Eq << Eq[3].subs(n, n + 2)

            
if __name__ == '__main__':
    prove(__file__)
