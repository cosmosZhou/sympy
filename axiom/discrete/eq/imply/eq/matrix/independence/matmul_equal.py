from util import *


@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args

    assert lhs.is_MatMul
    p_polynomial, *x = lhs.args

    assert rhs.is_MatMul
    _p_polynomial, *y = rhs.args
    x = MatMul(*x)
    y = MatMul(*y)

    assert p_polynomial == _p_polynomial

    assert p_polynomial.is_Lamda
    assert p_polynomial.shape
    assert x.shape == y.shape
    assert len(p_polynomial.shape) == 1
    assert len(x.shape) == 2
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.expr
    assert polynomial.is_Pow

    b, e = polynomial.as_base_exp()
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1

    return Equal(x, y)


@prove
def prove(Eq):
    from axiom import discrete
    p = Symbol(complex=True)
    m, n, k = Symbol(positive=True, integer=True)
    x, y = Symbol(shape=(n, m), given=True, complex=True)

    given = Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y)

    Eq << apply(given)

    Eq << Eq[0].T

    Eq << discrete.eq.imply.eq.matrix.independence.rmatmul_equal.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-10-30
