from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.concrete.expr_with_limits import Exists, Ref
from axiom import Algebre
from sympy.matrices.expressions.matmul import MatMul

@plausible
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args
    
    assert lhs.is_MatMul
    *x, p_polynomial = lhs.args
    
    assert rhs.is_MatMul
    *y, _p_polynomial = rhs.args
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_Ref
    assert p_polynomial.shape    
    assert len(p_polynomial.shape) == 1
    
    x = MatMul(*x)
    y = MatMul(*y)
    
    assert x.shape == y.shape
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
    p = Symbol("p")    
    m = Symbol('m', domain=Interval(1, oo, integer=True))
    n = Symbol('n', domain=Interval(1, oo, integer=True))
    x = Symbol("x", shape=(m, n))
    y = Symbol("y", shape=(m, n))
    k = Symbol('k', domain=Interval(1, oo, integer=True))
    
    given = Equality(x @ Ref[k:n](p ** k), y @ Ref[k:n](p ** k))
    
    Eq << apply(given)
    
    i = Symbol('i', integer=True)
    Eq << Eq[0][i]
    
    Eq << Algebre.vector.independence.rmatmul_equality.apply(Eq[-1])
    
    Eq << Eq[1][i:0:m]


if __name__ == '__main__':
    prove(__file__)
