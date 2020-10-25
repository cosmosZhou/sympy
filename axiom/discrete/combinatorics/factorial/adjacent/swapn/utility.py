from sympy.core.relational import Equality
from axiom.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import LAMBDA
from sympy.concrete.products import MatProduct
from axiom.algebre.matrix import elementary
from sympy import Symbol


@plausible
def apply(x, d, w=None):
    n = x.shape[0]
    m = d.shape[0]
    assert m.is_integer and m.is_finite
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)  
    k = Symbol.k(integer=True)

    if w is None:
        w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j:n, i:n](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    multiplier = MatProduct[i:m](w[i, d[i]])    
    return Equality(LAMBDA[k:n](x[(LAMBDA[k:n](k) @ multiplier)[k]]), x @ multiplier)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    assert n.is_integer    
    
    m = Symbol.m(domain=Interval(1, oo, integer=True))
    assert m.is_integer
    
    x = Symbol.x(complex=True, shape=(n,))
    d = Symbol.d(integer=True, shape=(oo,))
        
    Eq << apply(x, d[:m])    
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1][k]
    
    Eq << Eq[-1].subs(m, 1)
    
    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    d = Eq[1].rhs.args[1].function.indices[1].base
    Eq << elementary.swap.identity.apply(x, w, left=False, reference=None).subs(i, 0).subs(j, d[0])
    
    Eq << Eq[2].subs(m, m + 1)
    
    Eq << elementary.swap.identity_general.apply(x, LAMBDA[k](Eq[1].lhs.function.indices[0]).simplify(), w)
    
    Eq << Eq[-1].subs(i, m).subs(j, d[m])
    
    Eq << Eq[2].reference((k, 0, n - 1))
    
    Eq << Eq[-1].subs(Eq[1])

    
if __name__ == '__main__':
    prove(__file__)
