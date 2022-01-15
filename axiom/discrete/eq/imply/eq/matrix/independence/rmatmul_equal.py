from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)

    * x, p_polynomial = lhs.of(MatMul)

    * y, _p_polynomial = rhs.of(MatMul)

    assert p_polynomial == _p_polynomial

    assert p_polynomial.is_Lamda
    assert p_polynomial.shape
    assert len(p_polynomial.shape) == 1

    x = MatMul(*x)
    y = MatMul(*y)

    assert x.shape == y.shape
    assert len(x.shape) == 2
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.expr
    assert polynomial.is_Pow

    b, e = polynomial.as_base_exp()
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1

    if given.is_Exists:
        return Any(Equal(x, y), (x,), (y,))
    else:
        return Equal(x, y)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    p = Symbol(complex=True)
    m, n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(m, n))
    Eq << apply(Equal(x @ Lamda[k:n](p ** k), y @ Lamda[k:n](p ** k)))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[1], i)
    Eq << Eq[0][i]

    Eq << discrete.eq.imply.eq.vector.independence.rmatmul_equal.apply(Eq[-1])

    

    
    


if __name__ == '__main__':
    run()
# created on 2020-08-22
# updated on 2022-01-04