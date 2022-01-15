from util import *


@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args

    assert lhs.is_MatMul
    p_polynomial, x = lhs.args

    assert rhs.is_MatMul
    _p_polynomial, y = rhs.args

    assert p_polynomial == _p_polynomial

    assert p_polynomial.is_Lamda
    assert p_polynomial.shape == x.shape == y.shape
    assert len(p_polynomial.shape) == 1
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
    from axiom import algebra, discrete

    p = Symbol(complex=True)
    n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(n,), complex=True, given=True)
    assert x.is_given and y.is_given
    Eq << apply(Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y))

    i = Symbol(domain=Range(1, n + 1))
    Eq << Eq[0].subs(p, i)

    Eq << algebra.cond.imply.all.apply(Eq[-1], i)

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq.statement = Eq[-1].T

    i, k = Eq.statement.lhs.args[1].variables
    j = Symbol(integer=True)
    Eq << discrete.det_lamda.to.prod.vandermonde.st.linear.apply(Det(Lamda[j:n, i:n]((j + 1) ** i)))

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    j, i = Eq[-1].lhs.arg.variables
    Eq << Eq[-1].this.lhs.arg.limits_subs(i, k)

    Eq << Eq[-1].this.lhs.arg.limits_subs(j, i)

    Eq << algebra.ne_zero.eq.imply.eq.matrix.apply(Eq[-1], Eq.statement)

    
    


if __name__ == '__main__':
    run()
# created on 2020-08-21
# updated on 2022-01-15
