from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import algebre, discrete


@apply
def apply(x, d, w=None):
    n = x.shape[0]
    m = d.shape[0]
    assert m.is_integer and m.is_finite
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)  
    k = Symbol.k(integer=True)

    if w is None:
        w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    multiplier = MatProduct[i:m](w[i, d[i]])    
    return Equality(LAMBDA[k:n](x[(LAMBDA[k:n](k) @ multiplier)[k]]), x @ multiplier)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    assert n.is_integer    
    
    m = Symbol.m(domain=Interval(1, oo, integer=True))
    assert m.is_integer
    
    x = Symbol.x(complex=True, shape=(n,))
    d = Symbol.d(integer=True, shape=(oo,))
        
    Eq << apply(x, d[:m])    
    
    k = Eq[-1].lhs.variable
    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    multiplier = MatProduct[i:m](w[i, d[i]])
    Eq.hypothesis = Equality(x[(LAMBDA[k:n](k) @ multiplier)[k]], (x @ multiplier)[k], plausible=True)
    
    Eq.initial = Eq.hypothesis.subs(m, 1)
    
    d = Eq[1].rhs.args[1].function.indices[1].base
    Eq << discrete.matrix.elementary.swap.identity.apply(x, w, left=False, reference=None).subs(i, 0).subs(j, d[0])
    
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    Eq << discrete.matrix.elementary.swap.identity_general.apply(x, LAMBDA[k](Eq[1].lhs.function.indices[0]).simplify(), w)
    
    Eq << Eq[-1].subs(i, m).subs(j, d[m])
    
    Eq << algebre.equal.imply.equal.lamda.apply(Eq.hypothesis, (k, 0, n))
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq.induction.induct()

    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.initial, Eq[-1], n=m, start=1)

    
if __name__ == '__main__':
    prove(__file__)
