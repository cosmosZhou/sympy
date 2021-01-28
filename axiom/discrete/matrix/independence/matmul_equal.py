from sympy.core.numbers import oo
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import LAMBDA
from axiom import algebre, discrete
from sympy.matrices.expressions.matmul import MatMul
from sympy import Symbol

@apply(imply=True)
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args
    
    assert lhs.is_MatMul
    p_polynomial, *x = lhs.args
    
    assert rhs.is_MatMul
    _p_polynomial, *y = rhs.args
    x = MatMul(*x)
    y = MatMul(*y)
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_LAMBDA
    assert p_polynomial.shape
    assert x.shape == y.shape    
    assert len(p_polynomial.shape) == 1
    assert len(x.shape) == 2
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
    m = Symbol.m(positive=True, integer=True)
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(shape=(n, m), given=True, complex=True)
    y = Symbol.y(shape=(n, m), given=True, complex=True)
    k = Symbol.k(positive=True, integer=True)
    
    given = Equality(LAMBDA[k:n](p ** k) @ x, LAMBDA[k:n](p ** k) @ y)
    
    Eq << apply(given)
    
    Eq << Eq[0].T
    
    Eq << discrete.matrix.independence.rmatmul_equal.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)
