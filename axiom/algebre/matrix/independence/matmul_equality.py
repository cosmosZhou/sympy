from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.concrete.expr_with_limits import Exists, Ref
from axiom import algebre
from sympy.matrices.expressions.matmul import MatMul


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
    p = Symbol("p", complex=True)    
    m = Symbol('m', domain=Interval(1, oo, integer=True))
    n = Symbol('n', domain=Interval(1, oo, integer=True))
    x = Symbol("x", shape=(n, m), given=True, complex=True)
    y = Symbol("y", shape=(n, m), given=True, complex=True)
    k = Symbol('k', domain=Interval(1, oo, integer=True))
    
    given = Equality(Ref[k:n](p ** k) @ x, Ref[k:n](p ** k) @ y)
    
    Eq << apply(given)
    
    i = Symbol('i', integer=True)
    Eq << Eq[0][i]
    
    Eq << algebre.vector.independence.matmul_equality.apply(Eq[-1])
    
    Eq << Eq[1].T[i:0:m]


if __name__ == '__main__':
    prove(__file__)
