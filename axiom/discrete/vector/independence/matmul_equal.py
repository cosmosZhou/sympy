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
    polynomial = p_polynomial.function
    assert polynomial.is_Pow

    b, e = polynomial.as_base_exp()
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1

    return Equal(x, y)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    p = Symbol.p(complex=True)
    n = Symbol.n(domain=Range(1, oo))
    x = Symbol.x(shape=(n,), complex=True, given=True)
    y = Symbol.y(shape=(n,), complex=True, given=True)
    k = Symbol.k(domain=Range(1, oo))

    assert x.is_given and y.is_given

    given = Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y)

    Eq << apply(given)

    i = Symbol.i(domain=Range(1, n + 1))
    Eq << given.subs(p, i)

    Eq << Eq[-1].forall((i,))

    Eq << Eq[-1].this.function.apply(algebra.eq.imply.eq.lamda, *Eq[-1].limits, simplify=False)

    Eq << Eq[-1].this.lhs.astype(MatMul)

    Eq << Eq[-1].this.rhs.astype(MatMul)

    Eq.statement = Eq[-1].T

    i, k = Eq.statement.lhs.args[1].variables

    Eq << discrete.matrix.vandermonde.apply(Lamda[i:n](i + 1))

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    j, i = Eq[-1].lhs.arg.variables
    Eq << Eq[-1].this.lhs.arg.limits_subs(i, k)

    Eq << Eq[-1].this.lhs.arg.limits_subs(j, i)

    Eq << algebra.is_nonzero.eq.imply.eq.matrix.apply(Eq[-1], Eq.statement)


if __name__ == '__main__':
    run()
