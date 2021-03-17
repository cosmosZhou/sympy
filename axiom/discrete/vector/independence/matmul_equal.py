from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, discrete


@apply
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args        
    
    assert lhs.is_MatMul
    p_polynomial, x = lhs.args
    
    assert rhs.is_MatMul
    _p_polynomial, y = rhs.args
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_LAMBDA
    assert p_polynomial.shape == x.shape == y.shape    
    assert len(p_polynomial.shape) == 1
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.function
    assert polynomial.is_Power
    
    b, e = polynomial.as_base_exp()    
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    
    return Equality(x, y)


@prove
def prove(Eq):
    p = Symbol.p(complex=True)
    n = Symbol.n(domain=Interval(1, oo, integer=True))
    x = Symbol.x(shape=(n,), complex=True, given=True)
    y = Symbol.y(shape=(n,), complex=True, given=True)
    k = Symbol.k(domain=Interval(1, oo, integer=True))
    
    assert x.is_given and y.is_given
    
    given = Equality(LAMBDA[k:n](p ** k) @ x, LAMBDA[k:n](p ** k) @ y)
    
    Eq << apply(given)
    
    i = Symbol.i(domain=Interval(1, n, integer=True))
    Eq << given.subs(p, i)
    
    Eq << Eq[-1].forall((i,))
    
    Eq << Eq[-1].apply(algebre.eq.imply.eq.lamda, *Eq[-1].limits, simplify=False)
    
    Eq << Eq[-1].this.lhs.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.astype(MatMul)
    
    Eq.statement = Eq[-1].T
    
    i, k = Eq.statement.lhs.args[1].variables
    
    Eq << discrete.matrix.vandermonde.basicForm.apply(LAMBDA[i:n](i + 1))
    
    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    j, i = Eq[-1].lhs.arg.variables
    Eq << Eq[-1].this.lhs.arg.limits_subs(i, k)
    
    Eq << Eq[-1].this.lhs.arg.limits_subs(j, i)

    Eq << algebre.is_nonzero.eq.imply.eq.matrix.apply(Eq[-1], Eq.statement)
    

if __name__ == '__main__':
    prove(__file__)
