from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, discrete


@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args
    
    assert lhs.is_MatMul
    * x, p_polynomial = lhs.args
    
    assert rhs.is_MatMul
    * y, _p_polynomial = rhs.args
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_LAMBDA
    assert p_polynomial.shape    
    assert len(p_polynomial.shape) == 1
    
    x = MatMul(*x)
    y = MatMul(*y)
    
    assert x.shape == y.shape
    assert len(x.shape) == 2
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.function
    assert polynomial.is_Pow
    
    b, e = polynomial.as_base_exp()    
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    
    if given.is_Exists:
        return Exists(Equal(x, y), (x,), (y,))
    else:
        return Equal(x, y)


@prove
def prove(Eq):
    p = Symbol.p(complex=True)    
    m = Symbol.m(domain=Interval(1, oo, integer=True))
    n = Symbol.n(domain=Interval(1, oo, integer=True))
    x = Symbol.x(shape=(m, n))
    y = Symbol.y(shape=(m, n))
    k = Symbol.k(domain=Interval(1, oo, integer=True))
    
    Eq << apply(Equal(x @ LAMBDA[k:n](p ** k), y @ LAMBDA[k:n](p ** k)))
    
    i = Symbol.i(integer=True)
    Eq << Eq[0][i]
    
    Eq << discrete.vector.independence.rmatmul_equal.apply(Eq[-1])
    
    Eq << Eq[1][i:0:m]


if __name__ == '__main__':
    prove()
