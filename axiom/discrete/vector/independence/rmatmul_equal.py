from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from axiom import algebre, discrete
from sympy import LAMBDA
from sympy import Symbol


@apply
def apply(given):
    assert given.is_Equality
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
    assert polynomial.is_Power
    
    b, e = polynomial.as_base_exp()    
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    
    return Equality(x, y)




@prove
def prove(Eq):
    p = Symbol.p(complex=True)    
    n = Symbol.n(domain=Interval(1, oo, integer=True))
    x = Symbol.x(shape=(n,), given=True, complex=True)
    y = Symbol.y(shape=(n,), given=True, complex=True)
    k = Symbol.k(domain=Interval(1, oo, integer=True))
    
    given = Equality(x @ LAMBDA[k:n](p ** k), y @ LAMBDA[k:n](p ** k))
    
    Eq << apply(given)
    Eq << discrete.vector.cosine_similarity.apply(*given.lhs.args)
    Eq << discrete.vector.cosine_similarity.apply(*given.rhs.args)
    
    Eq << given.subs(Eq[-1], Eq[-2])
    
    Eq << discrete.vector.independence.matmul_equal.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)
