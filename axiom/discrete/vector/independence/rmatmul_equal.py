from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete


@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args
    
    assert lhs.is_MatMul
    x, p_polynomial = lhs.args
    
    assert rhs.is_MatMul
    y, _p_polynomial = rhs.args
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_LAMBDA
    assert p_polynomial.shape == x.shape == y.shape    
    assert len(p_polynomial.shape) == 1
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.function
    assert polynomial.is_Pow
    
    b, e = polynomial.as_base_exp()    
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    
    return Equal(x, y)


@prove
def prove(Eq):
    p = Symbol.p(complex=True)    
    n = Symbol.n(domain=Interval(1, oo, integer=True))
    x = Symbol.x(shape=(n,), given=True, complex=True)
    y = Symbol.y(shape=(n,), given=True, complex=True)
    k = Symbol.k(domain=Interval(1, oo, integer=True))
    
    Eq << apply(Equal(x @ LAMBDA[k:n](p ** k), y @ LAMBDA[k:n](p ** k)))
    
    Eq << discrete.vector.cosine_similarity.apply(*Eq[0].lhs.args)
    
    Eq << discrete.vector.cosine_similarity.apply(*Eq[0].rhs.args)
    
    Eq << Eq[0].subs(Eq[-1], Eq[-2])
    
    Eq << discrete.vector.independence.matmul_equal.apply(Eq[-1])


if __name__ == '__main__':
    prove()
