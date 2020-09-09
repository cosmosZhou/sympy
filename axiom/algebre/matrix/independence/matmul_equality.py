from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.concrete.expr_with_limits import Exists, Ref
from axiom import algebre
from sympy.matrices.expressions.matmul import MatMul
from sympy import var

@plausible
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
    
    assert p_polynomial.is_Ref
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
    
    if given.is_Exists:
        return Exists(Equality(x, y), (x,), (y,), given=given)
    else:
        return Equality(x, y, given=given)


from sympy.utility import check


@check
def prove(Eq):
    p = var(complex=True).p    
    m = var(domain=[1, oo], integer=True).m
    n = var(domain=[1, oo], integer=True).n
    x = var(shape=(n, m), given=True, complex=True).x
    y = var(shape=(n, m), given=True, complex=True).y
    k = var(domain=[1, oo], integer=True).k
    
    given = Equality(Ref[k:n](p ** k) @ x, Ref[k:n](p ** k) @ y)
    
    Eq << apply(given)
    
    i = var(integer=True).i
    Eq << Eq[0][i]
    
    Eq << algebre.vector.independence.matmul_equality.apply(Eq[-1])
    
    Eq << Eq[1].T[i:0:m]


if __name__ == '__main__':
    prove(__file__)
